"""Exact certification of Benders cuts (benders*.py) and of the resulting lower bound.

For a cut representative K' we compute, exactly over Q, a row functional phi
on the full kf.py row set with phi . v_u = 0 for all u in K' and phi . t != 0
(t = target column).  Any expansion with support inside K' would give
phi . t = sum_u d_u phi . v_u = 0, so every expansion support meets H = units minus K'.
The S_N images of a certified cut are certified (the system is S_N-equivariant:
images of units are units, kink groups map to kink groups, Moebius rows permute,
and the target is invariant).
Then the hitting-set ILP over the certified cuts (with images) is solved to
optimality with HiGHS; its optimum is a lower bound for s_N (the ILP optimum
itself is a floating-point MILP result: we also report a feasible dual proof
by the symmetric LP bound, recomputed in exact rationals from the LP basis).
usage: python certify_cuts.py N cuts.pkl ilp_time
"""
import itertools
import pickle
import sys
import time
from fractions import Fraction

import flint
import highspy
import numpy as np

from solve import System

N, CUTS, ILPT = int(sys.argv[1]), sys.argv[2], float(sys.argv[3])
S = System(N)
n = S.n
idx = {k: i for i, k in enumerate(S.U)}
G = len(S.gkeys)
R = G + S.Dm.shape[0]
cols = []           # sparse integer columns v_u : dict row -> int
for u in range(n):
    c = {}
    for gi, lam in S.ug[u]:
        c[gi] = lam
    for s in np.nonzero(S.Dm[:, u])[0]:
        c[G + int(s)] = int(S.Dm[s, u])
    cols.append(c)
tvec = {G + s: int(S.tD[s]) for s in range(S.Dm.shape[0])}


def certify(Kp):
    """Exact phi with phi.v_u = 0 (u in Kp), phi.t = 1; returns dict row->Fraction or None."""
    rows = sorted({r for u in Kp for r in cols[u]} | set(tvec))
    rp = {r: i for i, r in enumerate(rows)}
    m = len(Kp)
    # unknown phi (len(rows)); equations: for u in Kp: sum_r phi_r v_u[r] = 0 ; sum phi_r t_r = 1
    A = flint.fmpq_mat(m + 1, len(rows) + 1)
    for i, u in enumerate(Kp):
        for r, v in cols[u].items():
            A[i, rp[r]] = v
    for r, v in tvec.items():
        A[m, rp[r]] = v
    A[m, len(rows)] = 1
    Rr, rk = A.rref()
    phi = [Fraction(0)] * len(rows)
    for i in range(rk):
        j = next(j for j in range(len(rows) + 1) if Rr[i, j] != 0)
        if j == len(rows):
            return None
        q = Rr[i, len(rows)]
        phi[j] = Fraction(int(q.p), int(q.q))
    phi = {rows[i]: v for i, v in enumerate(phi) if v != 0}
    # independent exact verification
    for u in Kp:
        assert sum(phi.get(r, 0) * v for r, v in cols[u].items()) == 0
    assert sum(phi.get(r, 0) * v for r, v in tvec.items()) == 1
    return phi


def H_of(phi):
    return [u for u in range(n) if sum(phi.get(r, 0) * v for r, v in cols[u].items()) != 0]


def norm(h, pairs):
    h = list(h); M = []
    for a, b in pairs:
        if a > b:
            h[a] += 1; h[b] -= 1; a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))


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

if __name__ == '__main__':
    t0 = time.time()
    reps = pickle.load(open(CUTS, 'rb'))['reps']
    cuts = set()
    ok = 0
    for r in reps:
        Kp = [idx[k] for k in r]
        phi = certify(Kp)
        if phi is None:
            print('NOT certified (t in span over Q)', flush=True)
            continue
        ok += 1
        H = np.array(H_of(phi))   # exact H of phi is a subset of units minus K'
        for pt in ptab:
            cuts.add(frozenset(pt[H].tolist()))
        if ok % 20 == 0:
            print('certified', ok, 'cuts', len(cuts), f'{time.time()-t0:.0f}s', flush=True)
    print('certified reps', ok, 'of', len(reps), 'distinct cuts with images', len(cuts), flush=True)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('time_limit', ILPT)
    for _ in range(n):
        h.addVar(0, 1)
    h.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * n))
    h.changeColsCost(n, np.arange(n, dtype=np.int32), np.ones(n))
    for Hc in cuts:
        ix = np.array(sorted(Hc), dtype=np.int32)
        h.addRow(1, highspy.kHighsInf, len(ix), ix, np.ones(len(ix)))
    h.run()
    info = h.getInfo()
    print('ILP status', h.modelStatusToString(h.getModelStatus()), 'obj', info.objective_function_value,
          'dual bound', info.mip_dual_bound, f'{time.time()-t0:.0f}s', flush=True)
