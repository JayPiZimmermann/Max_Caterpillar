"""q_N = dim(V_N/A_N) by evaluation at random integer points, rank mod p.
Translation reduction: q_N = rank(A0 + F) - rank(A0) on {x_0 = 0}, where
A0 = span{relu(x_i - x_j) (i != j), x_i}, F = face functions (see dict.py).
The evaluation rank is always a valid lower bound for q_N (mod-p rank <= Q-rank,
and V/A -> Eval(V)/Eval(A) is onto); stability under more points is the
evidence for equality."""
import numpy as np, sys, time
from dict import keys
P_MOD = 2147483647

def rank_mod(M):
    M = M % P_MOD
    M = M.astype(np.int64)
    m, n = M.shape
    r = 0
    for c in range(n):
        if r == m: break
        piv = np.nonzero(M[r:, c])[0]
        if len(piv) == 0: continue
        p = r + piv[0]
        if p != r: M[[r, p]] = M[[p, r]]
        inv = pow(int(M[r, c]), P_MOD - 2, P_MOD)
        M[r] = (M[r] * inv) % P_MOD
        col = M[r + 1:, c].copy()
        nz = np.nonzero(col)[0]
        if len(nz):
            rows = r + 1 + nz
            M[rows] = (M[rows] - (col[nz, None] * M[r]) % P_MOD) % P_MOD
        r += 1
    return r

def evalF(ks, X):
    out = np.empty((len(ks), X.shape[0]), dtype=np.int64)
    for a, (h, M) in enumerate(ks):
        v = X @ np.array(h)
        for (i, j) in M:
            v = v + np.maximum(X[:, i] - X[:, j], 0)
        out[a] = np.maximum(v, 0)
    return out

def evalA0(N, X):
    rows = [X[:, i] for i in range(1, N)]
    for i in range(N):
        for j in range(i + 1, N):
            rows.append(np.maximum(X[:, i] - X[:, j], 0))
    return np.array(rows, dtype=np.int64)

def q(N, P, seed=0, R=10**6):
    rng = np.random.default_rng(seed)
    X = rng.integers(-R, R, size=(P, N)); X[:, 0] = 0
    ks = sorted(keys(N))
    A = evalA0(N, X); F = evalF(ks, X)
    ra = rank_mod(A.T.copy())  # transpose: columns = functions? rank same
    rf = rank_mod(np.vstack([A, F]).T.copy())
    return ra, rf, rf - ra, len(ks)

if __name__ == "__main__":
    N = int(sys.argv[1]); P = int(sys.argv[2])
    t = time.time()
    print(N, P, q(N, P, seed=int(sys.argv[3]) if len(sys.argv) > 3 else 0), round(time.time() - t, 1), flush=True)
