"""Necessary condition for max_N = L + d*sigma(G) (L, G one-hidden-layer, homogeneous):
odd parts give max+min - lam(x) between 0 and ell(x) for all x, lam, ell linear.
Search (lam, ell) minimizing the violation sum relu(M*(M-ell)) / scale on random points."""
import sys, numpy as np
from scipy.optimize import minimize
N = int(sys.argv[1]); rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
X = rng.standard_normal((4000, N))
S = X.max(1) + X.min(1)
def viol(p):
    lam, ell = p[:N], p[N:]
    M = S - X @ lam; L = X @ ell
    v = np.maximum(M * (M - L), 0.0)
    return v.mean()
best = (1e9, None)
for r in range(300):
    p0 = rng.standard_normal(2 * N) * rng.choice([0.3, 1, 3])
    res = minimize(viol, p0, method="Nelder-Mead", options={"maxiter": 20000, "xatol": 1e-10, "fatol": 1e-14})
    res = minimize(viol, res.x, method="Powell", options={"maxiter": 20000})
    if res.fun < best[0]: best = (res.fun, res.x)
print(N, "best violation", best[0]); print(np.round(best[1], 4))
