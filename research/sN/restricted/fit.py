"""MEASURED search: smallest k such that max_N = sum_k d_k relu(w_k . Phi) + R,
Phi = (x_i, relu(x_i-x_j)), R in span(relu(+-x_i), relu(x_i-x_j)).
Variable projection: outer weights solved by least squares; inner w by
scipy least_squares from random starts.  Output: best relative residual."""
import sys, itertools
import numpy as np
from scipy.optimize import least_squares

def feats(X):
    N = X.shape[1]
    pairs = list(itertools.combinations(range(N), 2))
    H = np.stack([np.maximum(X[:, i] - X[:, j], 0) for i, j in pairs], 1)
    Phi = np.concatenate([X, H], 1)
    Aux = np.concatenate([np.maximum(X, 0), np.maximum(-X, 0), H], 1)
    return Phi, Aux

def resid(wflat, Phi, Aux, y, k):
    W = wflat.reshape(k, -1)
    U = np.maximum(Phi @ W.T, 0)
    A = np.concatenate([U, Aux], 1)
    coef, *_ = np.linalg.lstsq(A, y, rcond=None)
    return A @ coef - y

def run(N, k, trials, seed, M=3000):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((M, N))
    Phi, Aux = feats(X)
    y = X.max(1)
    best = (np.inf, None)
    for t in range(trials):
        w0 = rng.standard_normal(k * Phi.shape[1])
        if rng.random() < 0.5:
            w0 = np.round(w0 * 1.5)
        r = least_squares(resid, w0, args=(Phi, Aux, y, k), method='lm', max_nfev=4000)
        val = np.linalg.norm(r.fun) / np.linalg.norm(y)
        if val < best[0]:
            best = (val, r.x)
    return best

if __name__ == '__main__':
    N, kmax, trials = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for k in range(1, kmax + 1):
        val, w = run(N, k, trials, seed=k)
        print(N, k, 'best rel residual %.3e' % val, flush=True)
        np.save('fit_N%d_k%d.npy' % (N, k), w)
