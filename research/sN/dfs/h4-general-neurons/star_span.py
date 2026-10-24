"""Is max_N in span(star neurons) + A?  Star neuron: relu(sum_j a_j relu(x_j - x_c)),
a in {-1,0,1}^{N-1} (or {-2..2}).  Measured lead (rank mod p on random integer points).
Usage: python star_span.py N [amax]"""
import sys, itertools
import numpy as np
from gn import *

N = int(sys.argv[1]); amax = int(sys.argv[2]) if len(sys.argv) > 2 else 1
W = []
for c in range(N):
    others = [j for j in range(N) if j != c]
    for vals in itertools.product(range(-amax, amax + 1), repeat=N - 1):
        if all(v >= 0 for v in vals):
            continue  # nonneg -> relu(g)=g in A
        if all(v <= 0 for v in vals):
            continue  # zero
        coef = [0] * N
        for j, v in zip(others, vals):
            coef[j] = v
        W.append(star(N, c, coef))
W = np.array(W)
print('N', N, 'stars', len(W))
m = len(W) + N + len(pairs(N)) + 50
X = sample(N, m, 1)
F = feats(X)
cols = [np.maximum(F @ W.T, 0), F]
M0 = np.concatenate(cols, 1)
mx = X.max(1)[:, None]
r0 = rank_np_mod_p(M0)
r1 = rank_np_mod_p(np.concatenate([M0, mx], 1))
rA = rank_np_mod_p(F)
print('rank A', rA, 'rank stars+A', r0, 'with max', r1, 'max in span:', r1 == r0)
