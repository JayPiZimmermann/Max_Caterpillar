"""Upper bounds: reweighted l1 on the sparse formulation, greedy pruning,
exact certification on all cells (Space.exact).
usage: python l1_sparse.py N iters seed [eps]"""
import sys, time, pickle
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack
from sparse_space import SparseSpace
from modp import Space

N, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
eps = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-2
ss = SparseSpace(N)
A = csr_matrix(ss.A.astype(float))
Aeq = hstack([A, -A]).tocsr()
b = ss.b.astype(float)
n = ss.n
rng = np.random.default_rng(seed)
w = 1 + 0.2 * rng.random(n)
best = None
t0 = time.time()
for it in range(iters):
    r = linprog(np.concatenate([w, w]), A_eq=Aeq, b_eq=b, bounds=(0, None), method='highs')
    x = r.x[:n] - r.x[n:]
    supp = [int(k) for k in np.argsort(np.abs(x)) if abs(x[k]) > 1e-7]   # small first
    ok = ss.feasible(supp)
    K = ss.prune(supp, order=supp) if ok else None
    print(f'it {it}: status {r.status} obj {r.fun:.4f} support {len(supp)} feasible {ok} pruned {len(K) if K else None} t={time.time()-t0:.0f}s', flush=True)
    if K and (best is None or len(K) < len(best)):
        best = K
        pickle.dump(best, open(f'data/l1s_best_{N}_{seed}.pkl', 'wb'))
    w = 1.0 / (np.abs(x) + eps) * (1 + 0.05 * rng.random(n))
print('best mod-P support', len(best), flush=True)
sp = Space(N)
res = sp.exact(best)
print('certified exactly on all cells:', res is not None, 'size', len(res[0]) if res else None, flush=True)
if res:
    pickle.dump((best, res), open(f'data/l1s_cert_{N}_{seed}.pkl', 'wb'))
