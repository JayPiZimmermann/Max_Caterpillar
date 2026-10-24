"""Exact lower bound for s_N by combinatorial Benders (hitting-set) cuts.

Model (kf.py): an expansion with unit support K exists iff the target column t
(0 on kink rows, (-1)^{|S|+1} on Moebius rows) lies in span{v_u : u in K}.
Cut: if K' is a set with t not in span(K'), every expansion support meets
H = units \\ K'.  We grow K' greedily (maximal infeasible superset of an
infeasible K) and add the cut together with its S_N images.
s_N >= optimum of the hitting-set ILP over the cuts found (each cut must be
certified exactly; see certify_cuts.py: a rational phi with phi.v_u = 0 on K'
and phi.t != 0).
usage: python benders2.py N iters cuts_per_iter ilp_time seed out.pkl
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
    return len(Hs), new


def ilp(tl):
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('time_limit', tl)
    h.setOptionValue('threads', 2)
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
    return K, info.mip_dual_bound, st


t0 = time.time()
K = []
best_lb = 0
for it in range(ITERS):
    if it > 0:
        K, lb, st = ilp(ILPT)
        if st == 'Optimal':
            best_lb = max(best_lb, len(K))
        else:
            best_lb = max(best_lb, int(np.ceil(lb - 1e-6)))
    sizes = []
    for c in range(CPI):
        order = rng.permutation(n).tolist()
        Kp = extend(K, order)
        if Kp is None:
            print('FEASIBLE support of size', len(K), '-> s_N <=', len(K), flush=True)
            pickle.dump({'K': [S.U[u] for u in K], 'feasible': True}, open(OUT + '.feasible', 'wb'))
            break
        sizes.append(add_cut(Kp))
    else:
        pickle.dump({'N': N, 'reps': [[S.U[u] for u in r] for r in reps], 'lb': best_lb},
                    open(OUT, 'wb'))
        print(f'it {it}: |K| {len(K)} lb {best_lb} cuts {len(cuts)} H-sizes {[s for s, _ in sizes]} '
              f't={time.time()-t0:.0f}s', flush=True)
        continue
    break
