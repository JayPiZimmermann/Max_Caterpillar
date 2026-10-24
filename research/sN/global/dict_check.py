#!/usr/bin/env python3
"""Independent check on the REAL dictionary (scripts/vocabulary_search.py):
for every normalized description k in dictionary(N) (auxiliary ones included),
evaluate D_L U_k directly (eval_key, exact integers) at every m-locality cube
and report max_k #{L : D_L U_k != 0} / (N-m)!, which must equal W_m(N) of
mixed_fast.py.  Also checks D_L max_N != 0 and D_L aux = 0 at every L.
Point: x_T = 0, x_o = -B^{rho(o)} * big, cube step 1 (i.e. delta = 1/big).
Usage: python3 dict_check.py N m
"""
import itertools
import math
import sys
from fractions import Fraction
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs

N, m = int(sys.argv[1]), int(sys.argv[2])
K0, _ = vs.dictionary(N)
keys = sorted(K0)
aux = vs.aux_functions(N)
B, big = 10 ** 3, 10 ** 6
cubes = []
for T in itertools.combinations(range(N), m):
    rest = [o for o in range(N) if o not in T]
    for order in itertools.permutations(rest):
        base = [0] * N
        for k, o in enumerate(order):
            base[o] = -B ** (k + 1) * big
        pts = []
        for sz in range(m + 1):
            for S in itertools.combinations(T, sz):
                y = list(base)
                for t in S:
                    y[t] += 1
                pts.append((tuple(y), (-1) ** (m - sz)))
        cubes.append(pts)


def D(f, pts):
    return sum(s * f(y) for y, s in pts)


assert all(D(vs.eval_max, pts) != 0 for pts in cubes)
assert all(D(lambda y, a=a: vs.eval_aux(a, y), pts) == 0 for pts in cubes for a in aux)
best = 0
for k in keys:
    c = sum(1 for pts in cubes if D(lambda y: vs.eval_key(k, y), pts) != 0)
    best = max(best, c)
print(f'N={N} m={m}: localities {len(cubes)}; keys {len(keys)}; '
      f'max passes per key = {best} = {Fraction(best, math.factorial(N - m))} (N-m)!; '
      f'D(max) != 0 and D(aux) = 0 at all localities')
