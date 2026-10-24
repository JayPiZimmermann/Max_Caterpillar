"""dim (V_N cap B_N), B_N = functions linear on every cell of {x_i = x_j, x_i = 0}
(basis: max(x_S) and max(0, x_S), S nonempty).  Measured (mod-p ranks of random evaluations).
Also: which max(x_S), max(0,x_S) lie in V_N (rank test)."""
import sys, itertools
import numpy as np
from common import keys, vs
from sym import eval_keys, run_rank
N = int(sys.argv[1])
ks = keys(N)
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(i + 1, N):
        e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
fam = aux + ks
Bf = []
for r in range(1, N + 1):
    for S in itertools.combinations(range(N), r):
        Bf.append((S, False)); Bf.append((S, True))
rng = np.random.default_rng(7)
npts = len(fam) + len(Bf) + 40
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
EV = eval_keys(fam, X)
EB = np.array([np.maximum(X[:, list(S)].max(axis=1), 0) if z else X[:, list(S)].max(axis=1) for S, z in Bf], dtype=np.int64)
rV, rVB = run_rank([EV, EB], f'braid{N}')
rB = run_rank([EB], f'braidB{N}')[0]
print(f'N={N} dimV={rV} dimB={rB} dim(V+B)={rVB} dim(V cap B)={rV + rB - rVB} dim(A)={len(aux)}')
# which basis elements of B lie in V
inV = []
for b in range(len(Bf)):
    r = run_rank([EV, EB[b:b + 1]], f'braidt{N}')[1]
    if r == rV: inV.append(Bf[b])
print('max functions in V:', [(''.join(map(str, S)), '0' if z else '') for S, z in inV])
