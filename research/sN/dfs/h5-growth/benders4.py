"""Exact lower bound for s_N by combinatorial Benders (hitting-set) cuts.

Model (kf.py): an expansion with unit support K exists iff the target column t
(0 on kink rows, (-1)^{|S|+1} on Moebius rows) lies in span{v_u : u in K}.
Cut: if K' is a set with t not in span(K'), every expansion support meets
H = units \\ K'.  We grow K' greedily (maximal infeasible superset of an
infeasible K) and add the cut together with its S_N images.
s_N >= optimum of the hitting-set ILP over the cuts found (each cut must be
certified exactly; see certify_cuts.py: a rational phi with phi.v_u = 0 on K'
and phi.t != 0).
usage: python benders4.py (optional 7th arg system pickle; env LOAD=prev.pkl reloads cuts) N iters cuts_per_iter ilp_time seed out.pkl
"""
import itertools
import pickle
import sys
import time

import flint
import highspy
import numpy as np

from solve import System

P = 2147483629
N, ITERS, CPI, ILPT, SEED, OUT = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
                                  float(sys.argv[4]), int(sys.argv[5]), sys.argv[6])
rng = np.random.default_rng(SEED)
if len(sys.argv) > 7:
    class _S:
        pass
    S = _S()
    S.U, S.groups, S.Dm, S.tD = pickle.load(open(sys.argv[7], 'rb'))
    S.n = len(S.U)
    S.gkeys = list(S.groups)
else:
    S = System(N)
n = S.n
R = len(S.gkeys) + S.Dm.shape[0]
A = np.zeros((R, n), dtype=np.int64)
for gi, g in enumerate(S.gkeys):
    for u, lam in S.groups[g].items():
        A[gi, u] = lam
A[len(S.gkeys):, :] = S.Dm
t = np.zeros(R, dtype=np.int64)
t[len(S.gkeys):] = S.tD
# independent rows of [A | t] mod P
At = np.concatenate([A, t[:, None]], axis=1) % P
M = flint.nmod_mat(n + 1, R, At.T.ravel().tolist(), P)
Rr, rk = M.rref()
I = []
for i in range(rk):
    j = next(j for j in range(R) if int(Rr[i, j]) != 0)
    I.append(j)
B = At[I, :n].copy()
AI = np.concatenate([A, t[:, None]], axis=1)[I].astype(float)  # integer rows (LP)
tt = At[I, n].copy()
print('N', N, 'units', n, 'rows', R, 'rank[A|t]', rk, flush=True)


def norm(h, pairs):
    h = list(h); Mm = []
    for a, b in pairs:
        if a > b:
            h[a] += 1; h[b] -= 1; a, b = b, a
        Mm.append((a, b))
    return (tuple(h), frozenset(Mm))


idx = {k: i for i, k in enumerate(S.U)}
perms = list(itertools.permutations(range(N)))
ptab = []
for p in perms:
    row = []
    for k in S.U:
        h, Mm = k
        h2 = [0] * N
        for i in range(N):
            h2[p[i]] = h[i]
        row.append(idx[norm(h2, [(p[a], p[b]) for a, b in Mm])])
    ptab.append(np.array(row))


def inv(a):
    return pow(int(a), P - 2, P)


import subprocess
proc = subprocess.Popen(['./extend'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
proc.stdin.write(f"{len(I)} {n}\n" + "\n".join(" ".join(map(str, row)) for row in B.tolist()) + "\n"
                 + " ".join(map(str, tt.tolist())) + "\n")
proc.stdin.flush()


def extend(K, order):
    """Greedy maximal infeasible superset of K (mod P) via ./extend. None if K feasible."""
    proc.stdin.write(f"{len(K)} " + " ".join(map(str, K)) + "\n" + " ".join(map(str, order)) + "\n")
    proc.stdin.flush()
    line = proc.stdout.readline().split()
    if line[0] == 'F':
        return None
    return [int(x) for x in line[2:]]



def lp_order(K, seed):
    """Weighted L1 cut LP: min sum_u w_u |phi.v_u| s.t. phi.v_u = 0 (u in K), phi.t = 1.
    Returns a greedy order: units by increasing |phi.v_u| (zeros first)."""
    r_ = AI.shape[0]
    g = np.random.default_rng(seed)
    w = g.exponential(1.0, n)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('time_limit', 120.0)
    inf = highspy.kHighsInf
    for _ in range(r_):
        h.addVar(-inf, inf)
    for u in range(n):
        h.addVar(0, inf)
    h.changeColsCost(n, np.arange(r_, r_ + n, dtype=np.int32), w)
    Kset = set(K)
    for u in range(n):
        col = AI[:, u]
        nz = np.nonzero(col)[0]
        if u in Kset:
            h.addRow(0, 0, len(nz), nz.astype(np.int32), col[nz])
        else:
            h.addRow(-inf, 0, len(nz) + 1, np.append(nz, r_ + u).astype(np.int32), np.append(col[nz], -1.0))
            h.addRow(0, inf, len(nz) + 1, np.append(nz, r_ + u).astype(np.int32), np.append(col[nz], 1.0))
    tc = AI[:, n]
    nz = np.nonzero(tc)[0]
    h.addRow(1, 1, len(nz), nz.astype(np.int32), tc[nz])
    h.run()
    x = np.array(h.getSolution().col_value[:r_])
    vals = np.abs(x @ AI[:, :n])
    order = sorted(range(n), key=lambda u: (vals[u] > 1e-7, w[u] * vals[u]))
    return order, int((vals <= 1e-7).sum())



orbit_of = -np.ones(n, dtype=int)
orbits = []
for u in range(n):
    if orbit_of[u] < 0:
        mem = sorted({int(pt[u]) for pt in ptab})
        for v in mem:
            orbit_of[v] = len(orbits)
        orbits.append(mem)
no = len(orbits)
orep_rows = []   # per cut representative: |H cap o| for each orbit o


def orbit_lp():
    """Symmetric LP relaxation (valid lower bound): min sum_o |o| y_o,
    sum_o |H cap o| y_o >= 1 for each cut representative H."""
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    for o in range(no):
        h.addVar(0, highspy.kHighsInf)
    h.changeColsCost(no, np.arange(no, dtype=np.int32), np.array([float(len(o)) for o in orbits]))
    for row in orep_rows:
        nz = np.nonzero(row)[0]
        h.addRow(1, highspy.kHighsInf, len(nz), nz.astype(np.int32), row[nz].astype(float))
    h.run()
    return h.getInfo().objective_function_value


cuts = []          # list of frozensets H (with images)
cutset = set()
reps = []          # (Kp) representatives for certification


def add_cut(Kp):
    H = np.ones(n, dtype=bool)
    H[Kp] = False
    Hs = np.nonzero(H)[0]
    new = 0
    for pt in ptab:
        img = frozenset(pt[Hs].tolist())
        if img not in cutset:
            cutset.add(img)
            cuts.append(img)
            new += 1
    reps.append(sorted(Kp))
    orep_rows.append(np.bincount(orbit_of[Hs], minlength=no))
    return len(Hs), new


def ilp(tl):
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('time_limit', tl)
    for _ in range(n):
        h.addVar(0, 1)
    h.changeColsIntegrality(n, np.arange(n, dtype=np.int32),
                            np.array([highspy.HighsVarType.kInteger] * n))
    h.changeColsCost(n, np.arange(n, dtype=np.int32), np.ones(n))
    for H in cuts:
        ix = np.array(sorted(H), dtype=np.int32)
        h.addRow(1, highspy.kHighsInf, len(ix), ix, np.ones(len(ix)))
    h.run()
    info = h.getInfo()
    x = h.getSolution().col_value
    K = [u for u in range(n) if x[u] > 0.5]
    st = h.modelStatusToString(h.getModelStatus())
    if not K: print('ILP status', st, info.mip_dual_bound, info.objective_function_value, flush=True)
    return K, info.mip_dual_bound, st




def greedy_hs(seed):
    """Randomized greedy hitting set of the current cuts (candidate generator)."""
    g = np.random.default_rng(seed)
    cnt = np.zeros(n)
    live = list(range(len(cuts)))
    hit = np.zeros(len(cuts), dtype=bool)
    mem = [[] for _ in range(n)]
    for ci, H in enumerate(cuts):
        for u in H:
            mem[u].append(ci)
    for u in range(n):
        cnt[u] = len(mem[u])
    K = []
    while not hit.all():
        best = np.flatnonzero(cnt == cnt.max())
        u = int(g.choice(best))
        K.append(u)
        for ci in mem[u]:
            if not hit[ci]:
                hit[ci] = True
                for v in cuts[ci]:
                    cnt[v] -= 1
    return K


import os
if os.environ.get('LOAD'):
    prev = pickle.load(open(os.environ['LOAD'], 'rb'))
    for r in prev['reps']:
        add_cut([idx[k] for k in r])
    print('reloaded', len(prev['reps']), 'reps', len(cuts), 'cuts', flush=True)
t0 = time.time()
best_lb = 0
for it in range(ITERS):
    cands = []
    if cuts:
        K, lb, st = ilp(ILPT)
        if st == 'Optimal':
            best_lb = max(best_lb, len(K))
        else:
            best_lb = max(best_lb, int(np.ceil(lb - 1e-6)))
        cands.append(K)
        for j in range(CPI - 1):
            cands.append(greedy_hs(int(rng.integers(1 << 30))))
    else:
        cands = [[] for _ in range(CPI)]
    sizes = []
    done = False
    for c, K in enumerate(cands):
        for mode in range(2):
            if mode == 0:
                order = rng.permutation(n).tolist()
            else:
                order, nzero = lp_order(K, int(rng.integers(1 << 30)))
            Kp = extend(K, order)
            if Kp is None:
                print('FEASIBLE support of size', len(K), '-> s_N <=', len(K), flush=True)
                pickle.dump({'K': [S.U[u] for u in K], 'feasible': True}, open(OUT + '.feasible', 'wb'))
                done = True
                break
            sizes.append((len(K),) + add_cut(Kp)[:1])
        if done:
            break
    if done:
        break
    lpv = orbit_lp()
    best_lb = max(best_lb, int(np.ceil(lpv - 1e-6)))
    pickle.dump({'N': N, 'reps': [[S.U[u] for u in r] for r in reps], 'lb': best_lb, 'lp': lpv},
                open(OUT, 'wb'))
    print(f'it {it}: LP {lpv:.3f} lb {best_lb} cuts {len(cuts)} (|K|,|H|) {sizes} '
          f't={time.time()-t0:.0f}s', flush=True)
