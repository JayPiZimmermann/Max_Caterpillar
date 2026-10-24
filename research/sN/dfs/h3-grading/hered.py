"""Heredity test: are the keys of V_{N-1} (in variables x_0..x_{N-2}, head padded by 0) in V_N?
Mod-p ranks of random integer evaluations (measured).  Usage: hered.py N"""
import sys
import numpy as np
from common import keys
from sym import eval_keys, run_rank
N = int(sys.argv[1])
ks = keys(N); kp = keys(N - 1)
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(i + 1, N):
        e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
emb = [(tuple(h) + (0,), M) for h, M in kp]
rng = np.random.default_rng(5)
X = rng.integers(-10**6, 10**6, size=(len(ks) + len(aux) + len(emb) + 50, N), endpoint=True).astype(np.int64)
blocks = [eval_keys(aux, X), eval_keys(ks, X), eval_keys(emb, X)]
r = run_rank(blocks, f'hered{N}')
print(f'N={N} dimA={r[0]} dimV={r[1]} dim(V+emb V_(N-1))={r[2]}  new={r[2]-r[1]}')
