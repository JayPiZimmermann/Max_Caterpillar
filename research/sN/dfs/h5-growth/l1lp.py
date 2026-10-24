"""One (re)weighted l1 LP (HiGHS IPM) on the kink formulation; saves the float
solution for downstream MILP/LNS (heuristic instrument).
usage: python l1lp.py N mode iters seed"""
import sys, time, pickle
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack
from solve import System
N, MODE, IT, SEED = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
S = System(N); n = S.n
rows, cols, vals = [], [], []
for r, g in enumerate(S.gkeys):
    for u, lam in S.groups[g].items():
        rows.append(r); cols.append(u); vals.append(lam)
Kink = csr_matrix((vals, (rows, cols)), shape=(len(S.gkeys), n), dtype=float)
SR = [S.Dm.shape[0] - 1] if MODE == 'top' else list(range(S.Dm.shape[0]))
A = vstack([Kink, csr_matrix(S.Dm[SR].astype(float))]).tocsr()
b = np.concatenate([np.zeros(Kink.shape[0]), S.tD[SR].astype(float)])
Aeq = hstack([A, -A]).tocsr()
rng = np.random.default_rng(SEED); w = 1 + 0.2 * rng.random(n)
t0 = time.time()
for it in range(IT):
    r = linprog(np.concatenate([w, w]), A_eq=Aeq, b_eq=b, bounds=(0, None), method='highs-ipm')
    x = r.x[:n] - r.x[n:]
    supp = np.flatnonzero(np.abs(x) > 1e-7)
    print(f'it {it} status {r.status} obj {r.fun:.4f} support {len(supp)} t={time.time()-t0:.0f}s', flush=True)
    pickle.dump({'x': x, 'it': it}, open(f'data/l1lp_{N}_{MODE}_{SEED}.pkl', 'wb'))
    w = (1.0 / (np.abs(x) + 1e-2)) * (1 + 0.3 * rng.random(n))
