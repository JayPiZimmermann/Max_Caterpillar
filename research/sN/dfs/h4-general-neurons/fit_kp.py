"""MEASURED: smallest k with max_N = sum_k d_k relu(w_k . Phi) + R (model A).
Variable projection with the Kaufman Jacobian (analytic), Levenberg-Marquardt
(scipy least_squares 'lm'), random restarts.  Points: Gaussian, normalized.
Floating point; a small residual is a lead, not a certificate.
Usage: python fit_kp.py N k trials [seed] [M]
"""
import sys, itertools, time
import numpy as np
from scipy.optimize import least_squares


def feats(X):
    N = X.shape[1]
    H = [np.maximum(X[:, i] - X[:, j], 0) for i, j in itertools.combinations(range(N), 2)]
    return np.concatenate([X, np.stack(H, 1)], 1)


def setup(N, M, rng):
    X = rng.standard_normal((M, N))
    X /= np.linalg.norm(X, axis=1, keepdims=True)
    return X, feats(X), X.max(1)


def solve(F, y, k, w0):
    D = F.shape[1]

    def parts(wflat):
        W = wflat.reshape(k, D)
        Z = F @ W.T
        G = np.maximum(Z, 0)
        B = np.concatenate([G, F], 1)
        coef, *_ = np.linalg.lstsq(B, y, rcond=None)
        r = B @ coef - y
        return W, Z, B, coef, r

    def fun(wflat):
        return parts(wflat)[4]

    def jac(wflat):
        W, Z, B, coef, r = parts(wflat)
        Q, _ = np.linalg.qr(B)
        act = (Z > 0).astype(float)
        J = np.empty((len(y), k * D))
        for j in range(k):
            Aj = (act[:, j:j + 1] * F) * coef[j]
            J[:, j * D:(j + 1) * D] = Aj - Q @ (Q.T @ Aj)
        return J

    r = least_squares(fun, w0, jac=jac, method='lm', max_nfev=200 * k * D)
    return r.x, np.linalg.norm(r.fun) / np.linalg.norm(y)


if __name__ == '__main__':
    N, k, trials = map(int, sys.argv[1:4])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    M = int(sys.argv[5]) if len(sys.argv) > 5 else 3000
    rng = np.random.default_rng(seed)
    X, F, y = setup(N, M, rng)
    # residual of the linear part alone, for scale
    c, *_ = np.linalg.lstsq(F, y, rcond=None)
    base = np.linalg.norm(F @ c - y) / np.linalg.norm(y)
    best = (np.inf, None)
    t0 = time.time()
    for t in range(trials):
        w0 = rng.standard_normal(k * F.shape[1])
        w, val = solve(F, y, k, w0)
        if val < best[0]:
            best = (val, w)
            np.save('fitkp_N%d_k%d.npy' % (N, k), w)
        print('N %d k %d trial %d rel %.3e best %.3e (linear-only %.3e) %.0fs' % (N, k, t, val, best[0], base, time.time() - t0), flush=True)
        if val < 1e-10:
            break
