#!/usr/bin/env python3
"""Closure test: add head-limit functions q = 1[<l,z> > 0] * L0(z) of twin germs
(L0 = <v0,z> + sum_F relu(z_i - z_j), l integer with l_apex = 0, sum l = 0, equal on some twin pair,
|l| <= Rl) to the twin family (|v| <= R).  Tests: S_m-symmetrised mixed differences over generic boxes
(random large integer anchors/steps).  If max is in the span, no functional continuous under these
limits (in particular no single functional working for all head sizes) separates.
Usage: twin_limit.py m R Rl ntests"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import rank_mod_p
import sym_md
from pn_test import forests

m, R, Rl, nt = map(int, sys.argv[1:5])
sym_md.MODE['pred'] = sym_md.twin_leaves
fam = sym_md.family(m, R)
rng = np.random.default_rng(5)
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=np.int64)
X = rng.integers(-10**5, 10**5, size=(nt, m)); D = rng.integers(1, 10**5, size=(nt, m))
perms = list(itertools.permutations(range(m)))
Zs = []
for p in perms:
    Xp, Dp = X[:, p], D[:, p]
    Zs.append((Xp[:, None, :] + Dp[:, None, :] * cube[None, :, :]).reshape(-1, m))
Zall = np.concatenate(Zs)

def feat(fn):
    vals = fn(Zall).reshape(len(perms), nt, len(cube)) @ sign
    return vals.sum(axis=0)

def L0(v, F, Z):
    s = Z @ np.array(v, dtype=np.int64)
    for i, j in F:
        s = s + np.maximum(Z[:, i] - Z[:, j], 0)
    return s

def twins(v, F):
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    sig = {}
    for (i, j) in F:
        if deg[i] == 1: sig.setdefault((j, 'o', v[i]), []).append(i)
        if deg[j] == 1: sig.setdefault((i, 'i', v[j]), []).append(j)
    return [tuple(x[:2]) for x in sig.values() if len(x) >= 2]

cols = [feat(lambda Z, v=v, F=F: np.maximum(L0(v, F, Z), 0)) for v, F in fam]
ng = len(cols)
ls = [l for l in itertools.product(range(-Rl, Rl + 1), repeat=m) if l[0] == 0 and sum(l) == 0 and any(l)]
nq = 0
for v, F in fam:
    for (a, b) in twins(v, F):
        for l in ls:
            if l[a] != l[b]: continue
            # keep the twin: v + lam*l has equal entries on a,b; q = 1[l.z>0] L0
            cols.append(feat(lambda Z, v=v, F=F, l=l: (Z @ np.array(l) > 0) * L0(v, F, Z))); nq += 1
A = np.array(cols, dtype=np.int64).T % 2147483629
b = feat(lambda Z: Z.max(axis=1))
r0 = rank_mod_p(A[:, :ng]); r0b = rank_mod_p(np.concatenate([A[:, :ng], b[:, None]], 1))
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b[:, None]], 1))
print(f'm={m} R={R} Rl={Rl}: {ng} germs (rank {r0}, +max {r0b}); +{nq} limit fns: rank {r1}, with max {r2} ->',
      'SEPARATED' if r2 > r1 else 'max IN span (closure)', flush=True)
