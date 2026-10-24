"""Sanity check of the locality equations (E) of k2_exact.py on a known identity (spec)."""
import sys, runpy, itertools
from fractions import Fraction as Fr
N = 5
s = runpy.run_path(sys.argv[1])
def v(l, a, S):
    return sum(Fr(l[i]) for i in S) + sum(Fr(c) for (i, j), c in a.items() if i in S and j not in S)
LOCS = [(frozenset(T), o) for T in itertools.combinations(range(N), 3) for o in range(N) if o not in T]
tot = {}
for d, l, a in s['NEURONS']:
    for T, o in LOCS:
        if v(l, a, T) == 0 and v(l, a, T | {o}) == 0:
            X = sum(max(v(l, a, {t}), 0) for t in T) - sum(max(v(l, a, set(P)), 0) for P in itertools.combinations(T, 2))
            tot[(T, o)] = tot.get((T, o), 0) + Fr(d) * X
print('all 20 equal 1:', all(tot.get(L, 0) == 1 for L in LOCS), sorted(set(tot.values())))
