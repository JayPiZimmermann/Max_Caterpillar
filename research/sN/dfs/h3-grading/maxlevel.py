"""Smallest j with max_N in F_j = A_N + span{U_k : |M_k| <= j}.  Since max_N and F_j are S_N-invariant,
max_N in F_j iff max_N in F_j^{S_N} = span of S_N-orbit sums (averaging an expansion).
Ranks mod p of random evaluations (measured; exact certificate via certify-style lifting not run)."""
import sys, json
import numpy as np
from common import keys
from sym import act_key, orbits, eval_keys, run_rank
N = int(sys.argv[1]); ks = keys(N)
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(N):
        if i != j:
            e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
fam = aux + ks; grade = [-1] * len(aux) + [len(k[1]) for k in ks]
gens = [tuple(list(range(t)) + [t + 1, t] + list(range(t + 2, N))) for t in range(N - 1)]
orbs = [o for o, _ in orbits(fam, act_key, gens)]
fidx = {k: n for n, k in enumerate(fam)}
rng = np.random.default_rng(5)
npts = len(orbs) + 40
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
E = eval_keys(fam, X)
cols = [(grade[fidx[next(iter(o))]], sum(E[fidx[k]] for k in o)) for o in orbs]
mx = X.max(axis=1)
out = {}
for j in sorted(set(g for g, _ in cols)):
    B = np.array([c for g, c in cols if g <= j])
    r0, r1 = run_rank([B, mx[None, :]], f'mx{N}')
    out[j] = (r0, r1, r1 == r0)
print(N, json.dumps({str(j): v for j, v in out.items()}))
