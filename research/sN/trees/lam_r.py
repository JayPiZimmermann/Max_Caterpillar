#!/usr/bin/env python3
"""Does the out-star functional Lambda kill germs with >= r out-leaves at a common centre?
Usage: lam_r.py m R r [D]"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
import sym_md
from sym_md import eval_germ
m, R, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
D = int(sys.argv[4]) if len(sys.argv) > 4 else m - 2
def pred(v, F):
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    cnt = {}
    for (i, j) in F:
        if deg[i] == 1 and v[i] == 0:
            cnt[j] = cnt.get(j, 0) + 1
    return any(x >= r for x in cnt.values())
sym_md.MODE['pred'] = pred
fam = sym_md.family(m, R)
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube])
deltas = [[1] * m] + [[D if i == t else 1 for i in range(m)] for t in range(m)]
coef = [-(m - 1)] + [1] * m
Z = np.concatenate([np.array(d)[None, :] * cube for d in deltas])
def lam(fn):
    return int(np.dot(coef, fn(Z).reshape(len(deltas), len(cube)) @ sign))
bad = 0; tot = 0
for v, F in fam:
    for perm in itertools.permutations(range(m)):
        vv = [0] * m
        for t in range(m): vv[perm[t]] = v[t]
        FF = [(perm[i], perm[j]) for i, j in F]
        tot += 1
        if lam(lambda Z: eval_germ(vv, FF, Z)) != 0: bad += 1
print(f'm={m} R={R} r={r} D={D}: Lambda(max)={lam(lambda Z: Z.max(axis=1))}; {bad}/{tot} germs nonzero')
