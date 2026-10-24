#!/usr/bin/env python3
"""Evaluate the out-star functional Lambda on the >=2-out-leaf germ family (all permutations)."""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from sym_md import family, eval_germ
m, R = int(sys.argv[1]), int(sys.argv[2])
D = int(sys.argv[3]) if len(sys.argv) > 3 else m - 2
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube])
deltas = [[1] * m] + [[D if i == t else 1 for i in range(m)] for t in range(m)]
coef = [-(m - 1)] + [1] * m
Z = np.concatenate([np.array(d)[None, :] * cube for d in deltas])
def lam(fn):
    vals = fn(Z).reshape(len(deltas), len(cube)) @ sign
    return int(np.dot(coef, vals))
print('Lambda(max) =', lam(lambda Z: Z.max(axis=1)))
bad = 0; tot = 0
for v, F in family(m, R):
    for perm in itertools.permutations(range(m)):
        vv = [0] * m
        for t in range(m): vv[perm[t]] = v[t]
        FF = [(perm[i], perm[j]) for i, j in F]
        x = lam(lambda Z: eval_germ(vv, FF, Z)); tot += 1
        if x != 0:
            bad += 1
            if bad <= 3: print('nonzero', x, vv, FF)
print(f'm={m} R={R} D={D}: {bad}/{tot} germs with Lambda != 0')
