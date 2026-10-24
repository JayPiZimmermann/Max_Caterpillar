"""General second-layer neurons over the pair-feature first layer (model A).

A neuron is relu(g) with g(x) = <l, x> + sum_{i<j} a_ij relu(x_i - x_j),
l, a integer (search leads only).  The remainder space is
A = span{x_i, relu(x_i - x_j)} (translation-equivariant reduction of the
auxiliary span, see NOTE.md in this directory).

Ranks are computed from exact integer evaluations modulo a prime P, hence are
certified LOWER bounds for the rational rank of the sampled matrix; a
membership "True" printed here is a measured lead, not a proof.
"""
import itertools
import numpy as np

P = 2_147_483_629


def pairs(N):
    return list(itertools.combinations(range(N), 2))


def feats(X):
    """Integer feature matrix [x_i, relu(x_i-x_j) (i<j)] for integer points X (m x N)."""
    N = X.shape[1]
    H = [np.maximum(X[:, i] - X[:, j], 0) for i, j in pairs(N)]
    return np.concatenate([X, np.stack(H, 1)], 1).astype(np.int64)


def neuron_vec(N, l, a):
    """Weight vector over feats for g = <l,x> + sum a_ij relu(x_i-x_j); a: dict."""
    pr = pairs(N)
    w = np.zeros(N + len(pr), dtype=np.int64)
    w[:N] = l
    for (i, j), v in a.items():
        if i < j:
            w[N + pr.index((i, j))] += v
        else:  # relu(x_i-x_j) = relu(x_j-x_i) + x_i - x_j
            w[N + pr.index((j, i))] += v
            w[i] += v
            w[j] -= v
    return w


def star(N, c, coef, lin=None):
    """g = sum_j coef[j] relu(x_j - x_c) (+ lin)."""
    a = {(j, c): coef[j] for j in range(N) if j != c and coef[j] != 0}
    l = np.zeros(N, dtype=np.int64) if lin is None else np.array(lin)
    return neuron_vec(N, l, a)


def sample(N, m, seed, B=10**5):
    rng = np.random.default_rng(seed)
    return rng.integers(-B, B, size=(m, N)).astype(np.int64)


def rank_mod_p(A):
    A = np.array(A, dtype=object) % P
    A = [list(map(int, r)) for r in A]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c]:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], P - 2, P)
        A[r] = [(v * inv) % P for v in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(u - f * v) % P for u, v in zip(A[i], A[r])]
        r += 1
        if r == rows:
            break
    return r


def rank_np_mod_p(M):
    """Fast rank mod P with numpy int64 (P < 2^31 so products fit after reduction)."""
    A = (np.array(M, dtype=np.int64) % P).copy()
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - (col[nzr, None] * A[r][None, :]) % P) % P
        r += 1
        if r == rows:
            break
    return r


def eval_neurons(X, W):
    """relu(feats(X) @ W.T), exact int64 (small weights)."""
    F = feats(X)
    return np.maximum(F @ np.array(W, dtype=np.int64).T, 0)
