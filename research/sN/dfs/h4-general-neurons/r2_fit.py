"""MEASURED: max_N = R + sum_{k<K} d_k relu(g_k), g_k, R in S = span{x_i - mean, relu(x_i-x_j)}
(translation-invariant neurons are WLOG, see report).  Variable projection + LM as in fit_kp.py,
points: Gaussian, projected to sum x = 0, normalized.  Saves best weights to r2_fit_N{N}_k{K}_s{seed}.npy.
Usage: python r2_fit.py N K trials seed [M] [timeout_s]"""
import sys, itertools, time
import numpy as np
from scipy.optimize import least_squares

def feats(X):
    N = X.shape[1]
    H = [np.maximum(X[:, i] - X[:, j], 0) for i, j in itertools.combinations(range(N), 2)]
    Xc = X - X.mean(1, keepdims=True)
    return np.concatenate([Xc[:, :-1], np.stack(H, 1)], 1)

def run(N, K, trials, seed, M=2500, tmax=5400):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((M, N)); X -= X.mean(1, keepdims=True); X /= np.linalg.norm(X, axis=1, keepdims=True)
    F = feats(X); y = X.max(1); D = F.shape[1]
    def parts(wf):
        Z = F @ wf.reshape(K, D).T
        B = np.concatenate([np.maximum(Z, 0), F], 1)
        c, *_ = np.linalg.lstsq(B, y, rcond=None)
        return Z, B, c, B @ c - y
    def fun(wf): return parts(wf)[3]
    def jac(wf):
        Z, B, c, r = parts(wf)
        Q, _ = np.linalg.qr(B)
        J = np.empty((M, K * D))
        for j in range(K):
            Aj = ((Z[:, j:j+1] > 0) * F) * c[j]
            J[:, j*D:(j+1)*D] = Aj - Q @ (Q.T @ Aj)
        return J
    best = np.inf; t0 = time.time()
    for t in range(trials):
        if time.time() - t0 > tmax: break
        w0 = rng.standard_normal(K * D)
        r = least_squares(fun, w0, jac=jac, method='lm', max_nfev=100 * K * D)
        val = np.linalg.norm(r.fun) / np.linalg.norm(y)
        if val < best:
            best = val; np.save('r2_fit_N%d_k%d_s%d.npy' % (N, K, seed), r.x)
        print('N %d k %d trial %d rel %.3e best %.3e %.0fs' % (N, K, t, val, best, time.time() - t0), flush=True)
        if val < 1e-10: break

if __name__ == '__main__':
    a = sys.argv[1:]
    run(int(a[0]), int(a[1]), int(a[2]), int(a[3]), *(int(x) for x in a[4:]))
