"""g2-superexponential: full-support content of caterpillar expansions.

Mixed differences  M_{y,d}(f) = sum_{S subset [k]} (-1)^{k-|S|} f(y + sum_{i in S} d_i e_i)
annihilate every function that does not depend on some coordinate.  For integer y, d the
values on keys are integers, so ranks are computed exactly modulo a prime.

Producer: research/sN/general/g2-superexponential/mixed.py (seeded, see main()).
Keys: research/sN/dfs/h3-grading/keys_k.pkl (normalized descriptions (h, M), M pairs (i, j)
meaning relu(y_i - y_j)), produced by keysfast.py / vocabulary_search.dictionary.
"""
import itertools, pickle, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
KEYS = os.path.join(HERE, '..', '..', 'dfs', 'h3-grading')
P = 2147483629  # prime < 2^31


def load_keys(k):
    return pickle.load(open(os.path.join(KEYS, f'keys_{k}.pkl'), 'rb'))


def eval_keys(keys, X):
    """X: (n, k) integer points -> (n, len(keys)) int64 values."""
    n, k = X.shape
    H = np.array([h for h, _ in keys], dtype=np.int64)  # (K, k)
    out = X @ H.T
    for c, (_, M) in enumerate(keys):
        s = np.zeros(n, dtype=np.int64)
        for i, j in M:
            s += np.maximum(X[:, i] - X[:, j], 0)
        out[:, c] += s
    return np.maximum(out, 0)


def mixed_rows(f_eval, Y, D):
    """Y, D: (m, k). Returns (m, F) matrix of mixed differences."""
    m, k = Y.shape
    acc = None
    for S in itertools.product([0, 1], repeat=k):
        S = np.array(S)
        V = f_eval(Y + D * S)
        sgn = (-1) ** (k - S.sum())
        acc = sgn * V if acc is None else acc + sgn * V
    return acc


def rank_modp(A):
    A = np.array(A, dtype=np.int64) % P
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        nz = np.nonzero(A[:, c])[0]
        for i in nz:
            if i != r:
                A[i] = (A[i] - A[i, c] * A[r]) % P
        r += 1
        if r == rows:
            break
    return r


def support(key):
    h, M = key
    s = {i for i, a in enumerate(h) if a}
    for i, j in M:
        s |= {i, j}
    return frozenset(s)


def samples(k, m, seed, amp=30):
    rng = np.random.default_rng(seed)
    Y = rng.integers(-amp, amp + 1, size=(m, k))
    D = rng.integers(1, amp + 1, size=(m, k)) * rng.choice([-1, 1], size=(m, k))
    return Y, D
