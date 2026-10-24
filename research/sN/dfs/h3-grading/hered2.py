"""dim(A_N + sum_{|S|=N-1} V_S) where V_S = keys of N-1 variables placed on S (padded heads), and
whether these padded keys are literally in the dictionary K_0(N).  Mod-p ranks (measured).
Usage: hered2.py N"""
import sys
import numpy as np
from common import keys
from sym import eval_keys, run_rank
N = int(sys.argv[1])
ks = keys(N); kset = set(ks); kp = keys(N - 1)
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(i + 1, N):
        e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
emb = set()
for drop in range(N):
    S = [v for v in range(N) if v != drop]
    for h, M in kp:
        H = [0] * N
        for a, v in enumerate(S): H[v] = h[a]
        emb.add((tuple(H), frozenset((S[i], S[j]) for i, j in M)))
emb = sorted(emb, key=lambda k: (k[0], sorted(k[1])))
print('padded keys', len(emb), 'of which literally in K_0(N):', sum(1 for k in emb if k in kset))
rng = np.random.default_rng(7)
X = rng.integers(-10**6, 10**6, size=(len(emb) + len(aux) + 50, N), endpoint=True).astype(np.int64)
r = run_rank([eval_keys(aux, X), eval_keys(emb, X)], f'hered2{N}')
print(f'N={N} dimA={r[0]} dim(A+sum V_S)={r[1]} quotient={r[1]-r[0]}')
