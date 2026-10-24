"""Lower bound for q_N (N=6) by incremental RREF mod p=524287 with exact
float64 BLAS products (p^2 * P < 2^53). Points: P random primitive points of
the grid [-R,R]^{N-1}, x_0 = 0. Prints rank(A0), rank(A0+F) as it goes."""
import numpy as np, sys, time
from dict import keys
from rank import evalF, evalA0
from rank_grid import grid
p = 524287
N, R, P, seed = map(int, sys.argv[1:5])
rng = np.random.default_rng(seed)
G = grid(N, R)
X = G[rng.choice(len(G), size=min(P, len(G)), replace=False)]
P = len(X)
ks = sorted(keys(N))
B = np.zeros((0, P)); piv = []
def add(rows):
    global B, piv
    rows = np.mod(rows.astype(np.float64), p)
    if len(piv):
        rows = np.mod(rows - np.mod(rows[:, piv], p) @ B, p)
    new = []
    for i in range(rows.shape[0]):
        r = rows[i]
        for (c, nr) in new:
            if r[c]: r = np.mod(r - r[c] * nr, p)
        nz = np.nonzero(r)[0]
        if len(nz) == 0: continue
        c = int(nz[0]); inv = pow(int(r[c]), p - 2, p)
        r = np.mod(r * inv, p)
        new = [(c2, np.mod(nr - nr[c] * r, p)) for (c2, nr) in new]
        new.append((c, r))
    if not new: return
    Nr = np.array([nr for _, nr in new]); nc = [c for c, _ in new]
    if len(piv):
        B = np.mod(B - np.mod(B[:, nc], p) @ Nr, p)
    B = np.vstack([B, Nr]); piv = piv + nc
t = time.time()
add(evalA0(N, X)); ra = len(piv)
print("P", P, "rank A0", ra, flush=True)
bs = 400
for s in range(0, len(ks), bs):
    add(evalF(ks[s:s + bs], X))
    print(s + bs, "rank", len(piv), "q >=", len(piv) - ra, round(time.time() - t), flush=True)
