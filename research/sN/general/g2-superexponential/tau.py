"""tau_k: fewest caterpillar units u whose combination agrees with max_k modulo functions of
fewer than k coordinates (relaxed: the lower-support part is arbitrary).

Test: exact rank mod p of mixed-difference vectors.  For each candidate set C we check
rank([M(C) | M(max)]) == rank(M(C)).
Usage: python tau.py k nsamples seed maxsize
"""
import sys, itertools
import numpy as np
from mixed import *

k, m, seed, maxsize = map(int, sys.argv[1:5])
keys = load_keys(k)
Y, D = samples(k, m, seed)
Mu = mixed_rows(lambda X: eval_keys(keys, X), Y, D)
Mmax = mixed_rows(lambda X: X.max(axis=1)[:, None], Y, D)[:, 0]
full = [c for c in range(len(keys)) if np.any(Mu[:, c])]
print('k', k, 'keys', len(keys), 'nonzero mixed', len(full), 'max nonzero', int(np.count_nonzero(Mmax)))
print('rank all', rank_modp(Mu[:, full]), 'rank +max', rank_modp(np.column_stack([Mu[:, full], Mmax])))
# dedupe proportional columns
seen = {}
for c in full:
    v = Mu[:, c]
    nz = np.nonzero(v)[0][0]
    g = np.gcd.reduce(np.abs(v))
    w = v // g * (1 if v[nz] > 0 else -1)
    seen.setdefault(w.tobytes(), c)
reps = list(seen.values())
print('distinct directions', len(reps))
mm = Mmax
for size in range(1, maxsize + 1):
    found = []
    for C in itertools.combinations(reps, size):
        A = Mu[:, list(C)]
        if rank_modp(np.column_stack([A, mm])) == rank_modp(A):
            found.append(C)
            if len(found) >= 3:
                break
    print('size', size, 'solutions (up to 3):', [[(keys[c][0], sorted(keys[c][1])) for c in C] for C in found], flush=True)
    if found:
        break
