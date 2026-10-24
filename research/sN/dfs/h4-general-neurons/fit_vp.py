"""MEASURED: smallest k with max_N = sum_k d_k relu(w_k . Phi) + R (model A),
Phi = (x_i, relu(x_i-x_j) i<j), R in span Phi.  Variable projection: for fixed W the
outer coefficients (d, R) are solved by least squares; W is optimized with
scipy least_squares (trf) on the projected residual, many random restarts.
Floating point; a small residual is a lead, not a certificate.
Usage: python fit_vp.py N kmin kmax trials [seed]
Saves best W per k to fitvp_N{N}_k{k}.npy
"""
import sys, itertools, time
import numpy as np
from scipy.optimize import least_squares


def feats(X):
    N = X.shape[1]
    H = [np.maximum(X[:, i] - X[:, j], 0) for i, j in itertools.combinations(range(N), 2)]
    return np.concatenate([X, np.stack(H, 1)], 1)


def run(N, k, trials, seed, M=2500):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((M, N))
    X /= np.linalg.norm(X, axis=1, keepdims=True)
    F = feats(X)
    y = X.max(1)
    D = F.shape[1]
    # project out span F once
    Qf, _ = np.linalg.qr(F)
    Pf = lambda v: v - Qf @ (Qf.T @ v)
    yp = Pf(y)

    def resid(wflat):
        W = wflat.reshape(k, D)
        G = Pf(np.maximum(F @ W.T, 0))
        d, *_ = np.linalg.lstsq(G, yp, rcond=None)
        return G @ d - yp

    best = (np.inf, None)
    for t in range(trials):
        w0 = rng.standard_normal(k * D)
        try:
            r = least_squares(resid, w0, method='trf', max_nfev=400 * k, diff_step=1e-7)
        except Exception:
            continue
        val = np.linalg.norm(r.fun) / np.linalg.norm(yp)
        if val < best[0]:
            best = (val, r.x)
        if val < 1e-9:
            break
    return best


if __name__ == '__main__':
    N, kmin, kmax, trials = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    for k in range(kmin, kmax + 1):
        t0 = time.time()
        val, p = run(N, k, trials, seed + 1000 * k)
        print(N, k, 'best rel projected residual %.3e' % val, 'time %.0fs' % (time.time() - t0), flush=True)
        np.save('fitvp_N%d_k%d.npy' % (N, k), p)
