"""MEASURED: search for zero-bias two-hidden-layer ReLU nets  max_N(x) = sum_k d_k relu(W_k . relu(A x)),
NO linear/skip terms.  Variable projection over d (output layer), Levenberg-Marquardt over (A, W)
with the Kaufman Jacobian; random restarts.  Points: Gaussian, normalized to the unit sphere.
Modes:  free  - A (h1 x N) free                                  (model B)
        phiA  - A fixed to the paper's Phi (h1 = C(N,2)+N+1)    (model A)
Floating point; a small residual is a lead, not a certificate.
Usage: python fit_B.py mode N h1 h2 trials seed [M] [tmax_s]   (h1 ignored for phiA)
Score = max(train relative residual, max abs error on 20000 fresh validation points).
Saves best (A, W, d) to fitB_<mode>_N_h1_h2_s<seed>.npz"""
import sys, time, itertools
import numpy as np
REG = 1e-6   # ridge on all weights (sqrt of lambda): suppresses closure-type blow-up solutions
from scipy.optimize import least_squares


def phi_rows(N):
    R = [np.eye(N)[0], -np.eye(N)[0]] + [np.eye(N)[i] - np.eye(N)[0] for i in range(1, N)]
    R += [np.eye(N)[i] - np.eye(N)[j] for i, j in itertools.combinations(range(N), 2)]
    return np.array(R)


def run(mode, N, h1, h2, trials, seed, M=3000, tmax=3600):
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((M, N)); X /= np.linalg.norm(X, axis=1, keepdims=True)
    y = X.max(1)
    Xv = rng.standard_normal((100000, N)); Xv /= np.linalg.norm(Xv, axis=1, keepdims=True)
    Xv = np.concatenate([Xv, np.outer([1, -1], np.ones(N)) / np.sqrt(N), (1 + 0.02 * rng.standard_normal((20000, N))) * rng.choice([-1, 1], (20000, 1))]); yv = Xv.max(1)
    Afix = phi_rows(N) if mode == 'phiA' else None
    if Afix is not None:
        h1 = len(Afix)
    nA = 0 if Afix is not None else h1 * N

    def unpack(th):
        A = Afix if Afix is not None else th[:nA].reshape(h1, N)
        W = th[nA:].reshape(h2, h1)
        return A, W

    def parts(th):
        A, W = unpack(th)
        Z1 = X @ A.T; H = np.maximum(Z1, 0)
        Z2 = H @ W.T; B = np.maximum(Z2, 0)
        Ba = np.concatenate([B, REG * np.eye(h2)]); ya = np.concatenate([y, np.zeros(h2)])
        d, *_ = np.linalg.lstsq(Ba, ya, rcond=None)
        return A, W, Z1, H, Z2, Ba, d, np.concatenate([Ba @ d - ya, REG * th])

    def fun(th):
        return parts(th)[-1]

    def jac(th):
        A, W, Z1, H, Z2, B, d, r = parts(th)
        Q, _ = np.linalg.qr(B)
        S2 = (Z2 > 0) * d  # M x h2 : d_k 1[z2_k>0]
        J = np.zeros((M + h2, nA + h2 * h1))
        if nA:
            G = (S2 @ W) * (Z1 > 0)  # M x h1 : dF/dz1_j
            J[:M, :nA] = (G[:, :, None] * X[:, None, :]).reshape(M, nA)
        J[:M, nA:] = (S2[:, :, None] * H[:, None, :]).reshape(M, h2 * h1)
        return np.concatenate([J - Q @ (Q.T @ J), REG * np.eye(nA + h2 * h1)])

    best = np.inf; t0 = time.time()
    tag = 'fitB_%s_N%d_h%d_%d_s%d' % (mode, N, h1, h2, seed)
    for t in range(trials):
        if time.time() - t0 > tmax:
            break
        th0 = rng.standard_normal(nA + h2 * h1)
        try:
            r = least_squares(fun, th0, jac=jac, method='lm', max_nfev=60 * (nA + h2 * h1))
        except Exception as e:
            print('trial', t, 'error', e); continue
        tr = np.linalg.norm(r.fun[:M]) / np.linalg.norm(y)
        A, W, *_, d, _ = parts(r.x)
        Fv = np.maximum(np.maximum(Xv @ A.T, 0) @ W.T, 0) @ d
        va = np.abs(Fv - yv).max()
        val = max(tr, va)   # validated: max abs error on 120002 fresh points (sphere, +-diagonal, near-diagonal)
        if val < best:
            best = val
            A, W, *_, d, _ = parts(r.x)
            np.savez(tag + '.npz', A=A, W=W, d=d, rel=val)
        print('%s trial %d train_rel %.3e val_maxabs %.3e best %.3e %.0fs' % (tag, t, tr, va, best, time.time() - t0), flush=True)
        if val < 1e-9:
            break
    return best


if __name__ == '__main__':
    a = sys.argv[1:]
    run(a[0], *(int(v) for v in a[1:6]), *(int(v) for v in a[6:]))
