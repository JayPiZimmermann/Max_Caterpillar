"""Relaxation: t_N(j) = min number of keys with |M| >= j needed so that max_N lies in
F_{j-1} + span(those keys).  Lower bound for s_N.  Here: test whether ONE key (per S_N-orbit) suffices,
and report the rank of the image of the top keys in gr_top.  Measured (mod-p ranks)."""
import sys
import numpy as np
from common import keys
from sym import act_key, orbits, eval_keys, run_rank
from sym import P
N = int(sys.argv[1]); j = int(sys.argv[2]); ks = keys(N)
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
rng = np.random.default_rng(9)
npts = len(low) + 200
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
EL = eval_keys(low, X) % P; mx = X.max(axis=1) % P
# project: reduce max and high keys modulo span(low) -- do via ranks per candidate (orbit reps)
gens = [tuple(list(range(t)) + [t + 1, t] + list(range(t + 2, N))) for t in range(N - 1)]
reps = [next(iter(o)) for o, _ in orbits(high, act_key, gens)]
EH = eval_keys(reps, X) % P
r0 = run_rank([EL], 'tn0')[0]
r1 = run_rank([EL, mx[None]], 'tn1')[1]
print('rank low', r0, 'with max', r1, 'orbit reps of high keys', len(reps))
ok = []
for n, k in enumerate(reps):
    a, b = run_rank([EL, EH[n:n+1], mx[None]], 'tn2')[1:]
    if a == b: ok.append(k)
print('single high keys (orbit reps) that suffice:', ok)
