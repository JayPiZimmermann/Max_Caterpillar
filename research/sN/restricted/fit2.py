"""MEASURED search (floating point, random starts): smallest k with
max_N = sum_k d_k relu(w_k . Phi) + R on sample points,
Phi = (x_i, relu(x_i-x_j)), R in span(relu(+-x_i), relu(x_i-x_j)).
Full Levenberg-Marquardt with analytic Jacobian.  Prints best relative residual.
Usage: python fit2.py N kmin kmax trials
"""
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


def make(Phi, Aux, y, k):
    D, A = Phi.shape[1], Aux.shape[1]

    def unpack(p):
        return p[:k * D].reshape(k, D), p[k * D:k * D + k], p[k * D + k:]

    def fun(p):
        W, d, c = unpack(p)
        return np.maximum(Phi @ W.T, 0) @ d + Aux @ c - y

    def jac(p):
        W, d, c = unpack(p)
        Z = Phi @ W.T
        act = (Z > 0).astype(float)
        JW = (act * d)[:, :, None] * Phi[:, None, :]
        return np.concatenate([JW.reshape(len(y), -1), np.maximum(Z, 0), Aux], 1)
    return fun, jac, D, A


def run(N, k, trials, seed, M=1500):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((M, N))
    Phi, Aux = feats(X)
    y = X.max(1)
    fun, jac, D, A = make(Phi, Aux, y, k)
    best = (np.inf, None)
    for t in range(trials):
        p0 = np.concatenate([rng.standard_normal(k * D), rng.standard_normal(k), np.zeros(A)])
        r = least_squares(fun, p0, jac=jac, method='lm', max_nfev=3000)
        val = np.linalg.norm(r.fun) / np.linalg.norm(y)
        if val < best[0]:
            best = (val, r.x)
    return best


if __name__ == '__main__':
    N, kmin, kmax, trials = map(int, sys.argv[1:5])
    for k in range(kmin, kmax + 1):
        val, p = run(N, k, trials, seed=100 + k)
        print(N, k, 'best rel residual %.3e' % val, flush=True)
        np.save('fit2_N%d_k%d.npy' % (N, k), p)
