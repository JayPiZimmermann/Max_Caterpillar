"""Refine a fit2 solution (MEASURED): more points, more LM iterations; print
residual and the normalized inner weights (each w_k scaled to max |entry| = 1)."""
import sys, itertools
import numpy as np
from scipy.optimize import least_squares
from fit2 import feats, make
N, k = int(sys.argv[1]), int(sys.argv[2])
p = np.load('fit2_N%d_k%d.npy' % (N, k))
rng = np.random.default_rng(7)
X = rng.standard_normal((6000, N))
Phi, Aux = feats(X); y = X.max(1)
fun, jac, D, A = make(Phi, Aux, y, k)
for it in range(5):
    r = least_squares(fun, p, jac=jac, method='lm', max_nfev=20000, xtol=1e-15, ftol=1e-15, gtol=1e-15)
    p = r.x
    print('rel residual %.3e' % (np.linalg.norm(r.fun) / np.linalg.norm(y)))
W = p[:k * D].reshape(k, D); d = p[k * D:k * D + k]
np.set_printoptions(precision=4, suppress=True, linewidth=200)
pairs = list(itertools.combinations(range(N), 2))
print('columns: x0..x%d then pairs' % (N - 1), pairs)
for w, dk in zip(W, d):
    s = np.abs(w).max()
    print('d*scale=%.5f' % (dk * s), w / s)
np.save('refined_N%d_k%d.npy' % (N, k), p)
