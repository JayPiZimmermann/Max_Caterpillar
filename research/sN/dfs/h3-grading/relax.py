"""Relaxed sparsity: t_N(j) = min #keys with |M| >= j whose span together with
F_{j-1} = A_N + span{U_k: |M_k| < j} contains max_N.  s_N >= t_N(j).  Mod-p computations (measured).
Search: exhaustive by size with the first key restricted to S_N-orbit representatives.
Usage: relax.py N j maxsize"""
import sys, itertools
import numpy as np
from common import keys, vs
from sym import act_key, orbits, eval_keys, P
N = int(sys.argv[1]); j = int(sys.argv[2]); smax = int(sys.argv[3]); ks = keys(N)
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for jj in range(N):
        if i != jj:
            e = [0] * N; e[i] = 1; e[jj] = -1; aux.append((tuple(e), frozenset()))
low = aux + [k for k in ks if len(k[1]) < j]
high = [k for k in ks if len(k[1]) >= j]
rng = np.random.default_rng(11)
npts = len(low) + len(high) + 40
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
EL = eval_keys(low, X) % P
EH = eval_keys(high, X) % P
mx = X.max(axis=1) % P
R, piv = vs.rref_mod_p(EL)          # rows: reduced basis of span(low) in point space
def reduce(v):
    v = v.copy() % P
    for r, pc in enumerate(piv):
        if v[pc]: v = (v - v[pc] * R[r]) % P
    return v
Hres = np.array([reduce(v) for v in EH]); b = reduce(mx)
# compress to the span of residuals
RR, pv = vs.rref_mod_p(np.vstack([Hres, b[None]]))
print(f'N={N} j={j}: low rank {len(piv)}, quotient dim (high span) {len(vs.rref_mod_p(Hres)[1])}, high keys {len(high)}', flush=True)
cols = np.array(pv)
H = Hres[:, cols] % P; bb = b[cols] % P
def rk(M):
    return len(vs.rref_mod_p(M)[1])
gens = [tuple(list(range(t)) + [t + 1, t] + list(range(t + 2, N))) for t in range(N - 1)]
hidx = {k: n for n, k in enumerate(high)}
reps = [hidx[next(iter(o))] for o, _ in orbits(high, act_key, gens)]
for s in range(1, smax + 1):
    found = None; cnt = 0
    for f in reps:
        others = [i for i in range(len(high)) if i != f]
        for rest in itertools.combinations(others, s - 1):
            S = [f] + list(rest); cnt += 1
            A = H[S]
            if rk(A) == rk(np.vstack([A, bb[None]])):
                found = S; break
        if found: break
    print(f'size {s}: checked {cnt}, found {found and [high[i] for i in found]}', flush=True)
    if found: break
