"""MEASURED: free-remainder search
    max_N(x) = <c0,x> + sum_j c_j relu(a_j.x) + sum_{k<K} d_k relu(<mu_k,x> + sum_j W_kj relu(a_j.x)).
Mode 'pairs': rows a_j = e_i - e_j (i<j) fixed  -> k(N) of the free-remainder pair model; by the
   reduction in RESULTS.md, model (A) needs exactly k(N)+2 second-layer neurons.
Mode 'free': h1 free rows (general first layer, model (B) remainder count k_B).
Variable projection over (c0, c, d); LM over (rows, mu, W); validation = max abs error on fresh points.
Usage: python fit_R.py mode N h1 K trials seed [M] [tmax]"""
import sys, time, itertools
import numpy as np
REG = 1e-6   # ridge (sqrt lambda) on all weights; suppresses closure-type blow-up
from scipy.optimize import least_squares


def run(mode, N, h1, K, trials, seed, M=3000, tmax=3600):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((M, N)); X /= np.linalg.norm(X, axis=1, keepdims=True); y = X.max(1)
    Xv = rng.standard_normal((100000, N)); Xv /= np.linalg.norm(Xv, axis=1, keepdims=True)
    Xv = np.concatenate([Xv, np.outer([1, -1], np.ones(N)) / np.sqrt(N), (1 + 0.02 * rng.standard_normal((20000, N))) * rng.choice([-1, 1], (20000, 1))]); yv = Xv.max(1)
    if mode == 'pairs':
        Afix = np.array([np.eye(N)[i] - np.eye(N)[j] for i, j in itertools.combinations(range(N), 2)]); h1 = len(Afix)
    else:
        Afix = None
    nA = 0 if Afix is not None else h1 * N
    D = N + h1  # neuron input features: x and relu rows

    def unpack(th):
        A = Afix if Afix is not None else th[:nA].reshape(h1, N)
        V = th[nA:].reshape(K, D)  # [mu | W]
        return A, V

    def parts(th, X=X, y=y):
        A, V = unpack(th)
        Z1 = X @ A.T; H = np.maximum(Z1, 0)
        Fe = np.concatenate([X, H], 1)
        Z2 = Fe @ V.T
        B = np.concatenate([np.maximum(Z2, 0), Fe], 1)
        nc = B.shape[1]
        Ba = np.concatenate([B, REG * np.eye(nc)]); ya = np.concatenate([y, np.zeros(nc)])
        c, *_ = np.linalg.lstsq(Ba, ya, rcond=None)
        return A, V, Z1, Fe, Z2, Ba, c, np.concatenate([Ba @ c - ya, REG * th])

    def fun(th):
        return parts(th)[-1]

    def jac(th):
        A, V, Z1, Fe, Z2, B, c, r = parts(th)
        Q, _ = np.linalg.qr(B)
        d = c[:K]; cl = c[K + N:]  # skip coefficients of relu rows
        S2 = (Z2 > 0) * d
        J = np.zeros((B.shape[0], nA + K * D))
        if nA:
            G = (S2 @ V[:, N:] + cl) * (Z1 > 0)
            J[:M, :nA] = (G[:, :, None] * X[:, None, :]).reshape(M, nA)
        J[:M, nA:] = (S2[:, :, None] * Fe[:, None, :]).reshape(M, K * D)
        return np.concatenate([J - Q @ (Q.T @ J), REG * np.eye(nA + K * D)])

    best = np.inf; t0 = time.time(); tag = 'fitR_%s_N%d_h%d_K%d_s%d' % (mode, N, h1, K, seed)
    for t in range(trials):
        if time.time() - t0 > tmax:
            break
        th0 = rng.standard_normal(nA + K * D)
        r = least_squares(fun, th0, jac=jac, method='lm', max_nfev=60 * (nA + K * D))
        tr = np.linalg.norm(r.fun[:M]) / np.linalg.norm(y)
        A, V, *_, c, _ = parts(r.x)
        Fev = np.concatenate([Xv, np.maximum(Xv @ A.T, 0)], 1)
        Bv = np.concatenate([np.maximum(Fev @ V.T, 0), Fev], 1)
        va = np.abs(Bv @ c - yv).max()
        val = max(tr, va)
        if val < best:
            best = val; np.savez(tag + '.npz', A=A, V=V, c=c, val=val)
        print('%s trial %d train_rel %.3e val_maxabs %.3e best %.3e %.0fs' % (tag, t, tr, va, best, time.time() - t0), flush=True)
        if val < 1e-8:
            break


if __name__ == '__main__':
    a = sys.argv[1:]
    run(a[0], *(int(v) for v in a[1:6]), *(int(v) for v in a[6:]))
