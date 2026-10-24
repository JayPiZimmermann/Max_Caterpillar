"""Localisation test for gr_j = F_j/F_{j-1}, F_j = A_N + span{U_k : |M_k| <= j}.
For every span W = span(h, e_i - e_j : (i,j) in M) of a grade-j key (dim W = j+1) take a random
generic point x0 of L = W^perp (scale 1e7) and points x0 + z, z in W small (W-basis coords in [-60,60]).
loc_W = rank(germs of F_j at x0) - rank(germs of F_{j-1} at x0) (constants included in the base).
Prediction: dim gr_j = sum_W loc_W.  Mod-p ranks (measured).  With m > 1, m random points x0 of L are used jointly (germs in several chambers of L).
Usage: localj.py N j [npts per x0] [m]"""
import sys, collections
import numpy as np
from common import keys
from sym import eval_keys, run_rank
import contextlib, io
with contextlib.redirect_stdout(io.StringIO()):
    sys_argv = sys.argv; sys.argv = sys.argv[:1]; from flats import rref; sys.argv = sys_argv
N = int(sys.argv[1]); J = int(sys.argv[2]); npts = int(sys.argv[3]) if len(sys.argv) > 3 else 300; m = int(sys.argv[4]) if len(sys.argv) > 4 else 1
ks = keys(N); DEBUG = len(sys.argv) > 5
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(i + 1, N):
        e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
low = aux + [k for k in ks if len(k[1]) < J]
top = [k for k in ks if len(k[1]) == J]
def gens(k):
    rows = [list(k[0])]
    for i, j in k[1]:
        e = [0] * N; e[i] = 1; e[j] = -1; rows.append(e)
    return rows
byW = collections.defaultdict(list)
for k in top: byW[rref(gens(k))].append(k)
rng = np.random.default_rng(17)
tot = 0; hist = collections.Counter(); sat = 0
for W, kk in byW.items():
    B = np.array(gens(kk[0]), dtype=np.int64)            # integer basis of W (j+1 x N)
    # basis of L = W^perp: null space via SVD then integer-ish random point: project random vector
    Wf = B.astype(float); Q, _ = np.linalg.qr(Wf.T)
    G = B @ B.T; det = int(round(np.linalg.det(G)))
    adj = np.round(np.linalg.inv(G) * det).astype(np.int64)
    Xs = []
    for _ in range(m):
        v = rng.normal(size=N); v = v - Q @ (Q.T @ v)
        vi = np.round(v * 1e4).astype(np.int64)
        x0 = det * vi - B.T @ (adj @ (B @ vi))
        assert not np.any(B @ x0)
        x0 = x0 * max(1, int(1e7 // max(1, np.abs(x0).max())))
        c = rng.integers(-60, 61, size=(npts, len(B)))
        Xs.append(x0[None, :] + c @ B)
    X = np.concatenate(Xs)
    if m == 1:   # keep only functions that are not affine near x0 (others lie in the affine base)
        x0r = X[:1] - (c[:1] @ B)
        def nonaff(fs):
            A = eval_keys(fs, x0r)[:, 0] if fs else np.zeros(0)
            H = np.array([f[0] for f in fs]); arg = H @ x0r[0]
            for n, f in enumerate(fs):
                arg[n] += sum(max(x0r[0, i] - x0r[0, j], 0) for i, j in f[1])
            tie = np.array([any(x0r[0, i] == x0r[0, j] for i, j in f[1]) for f in fs], dtype=bool)
            return [f for f, a, t in zip(fs, arg, tie) if a == 0 or t]
        lowf, topf = nonaff(low), nonaff(top)
    else:
        lowf, topf = low, top
    # affine functions per chamber point x0 (affine parts differ between chambers of L)
    ones = np.zeros((m * (N + 1), m * npts), dtype=np.int64)
    for t in range(m):
        ones[t * (N + 1), t * npts:(t + 1) * npts] = 1
        ones[t * (N + 1) + 1:(t + 1) * (N + 1), t * npts:(t + 1) * npts] = X[t * npts:(t + 1) * npts].T
    aff = np.concatenate([ones] + [X[None, :, i] for i in range(N)])
    base = np.concatenate([aff, eval_keys(lowf, X)]) if lowf else aff
    r = run_rank([base, eval_keys(topf, X)], f'locj_{N}_{J}')
    if r[1] >= m * npts - 5: sat += 1
    if DEBUG: print("   W", len(kk), "ranks", r, "x0 max", int(np.abs(X).max()))
    tot += r[1] - r[0]; hist[(len(kk), r[1] - r[0])] += 1
print(f'N={N} j={J} m={m} spans {len(byW)} predicted dim gr_j = {tot}; saturated spans {sat}; (#keys with span W, loc_W) histogram {sorted(hist.items())}', flush=True)
