"""Upper bounds on s_N: reweighted l1 LP for a sparse expansion, then greedy
pruning (mod P) and exact certification on all cells.
usage: python l1_upper.py N iters seed"""
import sys, time, pickle, random
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack as sh
from modp import Space
N, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
sp = Space(N)
S = sp.S
A = np.hstack([sp.EU[S], -sp.EU[S], sp.EA[S]]).astype(float)
b = sp.Em[S].astype(float)
n = sp.n; na = sp.EA.shape[1]
rng = np.random.default_rng(seed)
w = np.ones(n) * (1 + 0.1 * rng.random(n))
best = None
for it in range(iters):
    c = np.concatenate([w, w, np.zeros(na)])
    bounds = [(0, None)] * (2 * n) + [(None, None)] * na
    t0 = time.time()
    r = linprog(c, A_eq=csr_matrix(A), b_eq=b, bounds=bounds, method='highs')
    d = r.x[:n] - r.x[n:2 * n]
    supp = [int(k) for k in np.argsort(-np.abs(d)) if abs(d[k]) > 1e-7]
    ok = sp.feasible(supp)
    K = sp.prune(supp, order=supp[::-1]) if ok else None
    print(f'iter {it}: lp {r.status} obj {r.fun:.4f} support {len(supp)} feasible {ok} pruned {len(K) if K else None} ({time.time()-t0:.1f}s)', flush=True)
    if K and (best is None or len(K) < len(best)):
        best = K
    w = 1.0 / (np.abs(d) + 1e-3)
print('best mod-P support', len(best))
res = sp.exact(best)
print('exact certified on all cells:', res is not None)
if res:
    pickle.dump((best, res), open(f'data/l1_{N}_{seed}.pkl', 'wb'))
    print('certified support size', len(res[0]))
