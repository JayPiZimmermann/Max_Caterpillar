"""MEASURED: for a survivor pair of flats, search max_5 = R + sum_k d_k relu(g_k) with g_k restricted
to V_{Z_k} (few parameters), R free in span{x, relu(x_i-x_j)}; many restarts (LM, var-pro).
Usage: python fit_flat.py Z1,Z2,... [trials]"""
import sys, itertools, numpy as np
from scipy.optimize import least_squares
from k2_exact import F
N = 5; P = list(itertools.combinations(range(N), 2))
Zs = [int(a) for a in sys.argv[1].split(",")]; trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
Bs = [np.array([[float(c) for c in v] for v in F[Z][1]]) for Z in Zs]   # rows: (l, a) basis
rng = np.random.default_rng(0)
X = rng.standard_normal((4000, N)); X -= X.mean(1, keepdims=True); X /= np.linalg.norm(X, axis=1, keepdims=True)
H = np.stack([np.maximum(X[:, i] - X[:, j], 0) for i, j in P], 1); Fe = np.concatenate([X, H], 1); y = X.max(1)
dims = [B.shape[0] for B in Bs]
def parts(th):
    out = []; o = 0
    for B, m in zip(Bs, dims):
        w = th[o:o + m] @ B; o += m; out.append(np.maximum(Fe @ w, 0))
    A = np.concatenate([np.stack(out, 1), Fe], 1)
    c, *_ = np.linalg.lstsq(A, y, rcond=None)
    return A @ c - y
best = 9
for t in range(trials):
    r = least_squares(parts, rng.standard_normal(sum(dims)), method='lm')
    v = np.abs(r.fun).max(); best = min(best, v)
    if v < 1e-9: print('EXACT-LOOKING fit at trial', t, r.x); break
print('Z', Zs, 'dims', dims, 'best max abs residual', best)
