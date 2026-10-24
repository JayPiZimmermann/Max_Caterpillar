"""Sparsify an expansion support inside its affine solution space (upper bounds on s_N).

Input: a pickle with 'K' (unit keys) carrying some expansion of max_N (mode full)
or a top-active braid-linear combination (mode top).  Restrict the kf.py system to
K, compress the rows by a sparse random projection mod p (rank-preserving with
high probability; the final support is certified exactly), write the solution
set as x0 + Z y, and greedily impose x_u = 0 (in random orders, several
restarts).  The best support is re-solved exactly over Q (solve.System.solve)
and written out.
usage: python sparsify.py N mode in.pkl restarts seed out.pkl
"""
import pickle
import sys
import time

import flint
import numpy as np

from solve import System

P = 2147483629
N, MODE, INP, RESTARTS, SEED, OUT = (int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]),
                                     int(sys.argv[5]), sys.argv[6])
rng = np.random.default_rng(SEED)
t0 = time.time()
S = System(N)
idx = {k: i for i, k in enumerate(S.U)}
K = sorted(idx[k] for k in pickle.load(open(INP, 'rb'))['K'])
m = len(K)
pos = {u: i for i, u in enumerate(K)}
SR = [S.Dm.shape[0] - 1] if MODE == 'top' else list(range(S.Dm.shape[0]))
gis = sorted({gi for u in K for gi, _ in S.ug[u]})
print('N', N, 'support', m, 'rows', len(gis) + len(SR), f'{time.time()-t0:.0f}s', flush=True)
rp = m + 40
proj = np.zeros((rp, m + 1), dtype=np.int64)


def addrow(vals):
    """vals: dict col -> int. Add to 3 random projected rows with random coefficients."""
    for _ in range(3):
        r = int(rng.integers(rp))
        c = int(rng.integers(1, P))
        for j, v in vals.items():
            proj[r, j] = (proj[r, j] + c * (v % P)) % P


for gi in gis:
    addrow({pos[u]: lam for u, lam in S.groups[S.gkeys[gi]].items() if u in pos})
for s in SR:
    vals = {pos[u]: int(S.Dm[s, u]) for u in K if S.Dm[s, u]}
    vals[m] = int(S.tD[s])
    addrow(vals)
M = flint.nmod_mat(rp, m + 1, proj.ravel().tolist(), P)
R, rk = M.rref()
R = np.array([[int(R[i, j]) for j in range(m + 1)] for i in range(rk)], dtype=np.int64)
pivots = [int(np.nonzero(R[i])[0][0]) for i in range(rk)]
assert m not in pivots, 'support infeasible'
free = [j for j in range(m) if j not in set(pivots)]
# x = x0 + Z y : x0 pivots = R[:, m], free = 0 ; Z columns per free var
x0 = np.zeros(m, dtype=np.int64)
Z = np.zeros((m, len(free)), dtype=np.int64)
for i, pc in enumerate(pivots):
    x0[pc] = R[i, m]
    Z[pc, :] = (-R[i, free]) % P
for k, f in enumerate(free):
    Z[f, k] = 1
print('rank', rk, 'solution dim', len(free), f'{time.time()-t0:.0f}s', flush=True)


def greedy(order):
    x = x0.copy(); Zc = Z.copy()
    alive = np.ones(Zc.shape[1], dtype=bool)
    for u in order:
        row = Zc[u] * alive
        nz = np.nonzero(row)[0]
        if len(nz) == 0:
            continue
        j = nz[0]
        inv = pow(int(row[j]), P - 2, P)
        # eliminate y_j: y_j = -(x[u] + sum_{k!=j} Z[u,k] y_k)/Z[u,j]
        col = Zc[:, j].copy()
        f = (col * inv) % P
        x = (x - f * x[u]) % P
        Zc = (Zc - (f[:, None] * (row[None, :] % P)) % P) % P
        alive[j] = False
        Zc[:, j] = 0
    return [K[i] for i in range(m) if x[i] != 0]


best = None
for r in range(RESTARTS):
    order = rng.permutation(m).tolist()
    sup = greedy(order)
    if best is None or len(sup) < len(best):
        best = sup
    print('restart', r, 'support', len(sup), 'best', len(best), f'{time.time()-t0:.0f}s', flush=True)
sol = S.solve(best, SR)
assert sol is not None, 'exact re-solve failed (projection artefact?)'
best = [u for u in best if sol.get(u, 0) != 0]
print('exact support', len(best), flush=True)
pickle.dump({'N': N, 'mode': MODE, 'K': [S.U[u] for u in best], 'd': {S.U[u]: sol[u] for u in best}},
            open(OUT, 'wb'))
