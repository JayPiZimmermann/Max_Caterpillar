"""Reweighted-l1 heuristic for sparse solutions of the kink formulation.
mode 'top': KINK d = 0, D_[N] d = 1          (e_N problem)
mode 'full': KINK d = 0, D_S d = (-1)^{|S|+1}  (s_N problem)
Each candidate support is pruned greedily (mod-P rank tests), then solved
exactly over Q (solve.System.solve); stored solutions are exact.
usage: python l1.py N mode iters seed
"""
import pickle
import sys
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack

from solve import System, prune as prune_ms

N, MODE, ITERS, SEED = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
S = System(N)
n = S.n
rows, cols, vals = [], [], []
for r, g in enumerate(S.gkeys):
    for u, lam in S.groups[g].items():
        rows.append(r); cols.append(u); vals.append(lam)
Kink = csr_matrix((vals, (rows, cols)), shape=(len(S.gkeys), n), dtype=float)
SR = [S.Dm.shape[0] - 1] if MODE == 'top' else list(range(S.Dm.shape[0]))
A = vstack([Kink, csr_matrix(S.Dm[SR].astype(float))]).tocsr()
b = np.concatenate([np.zeros(Kink.shape[0]), S.tD[SR].astype(float)])
Aeq = hstack([A, -A]).tocsr()
rng = np.random.default_rng(SEED)
w = 1 + rng.random(n)
best = None
t0 = time.time()

for it in range(ITERS):
    r = linprog(np.concatenate([w, w]), A_eq=Aeq, b_eq=b, bounds=(0, None), method='highs-ipm')
    if r.status != 0:
        print('lp status', r.status)
        break
    x = r.x[:n] - r.x[n:]
    supp = [int(k) for k in np.flatnonzero(np.abs(x) > 1e-7)]
    order = sorted(supp, key=lambda k: abs(x[k]))
    res = prune_ms(S, supp, SR, order=order)
    K = res[0] if res else None
    print(f'it {it}: obj {r.fun:.4f} support {len(supp)} pruned {len(K) if K else None} t={time.time()-t0:.0f}s', flush=True)
    if K and (best is None or len(K) < len(best)):
        best = K
        sol = res[1]
        pickle.dump({'N': N, 'mode': MODE, 'K': [S.U[u] for u in best],
                     'd': {S.U[u]: sol[u] for u in best}},
                    open(f'data/l1_{N}_{MODE}_{SEED}.pkl', 'wb'))
    w = (1.0 / (np.abs(x) + 1e-2)) * (1 + 0.3 * rng.random(n))
print('best', len(best) if best else None)
