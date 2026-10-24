#!/usr/bin/env python3
"""Extract a small-support separating unit-cube functional W at m, R, spread k (step 14).
Greedy removal of anchor orbits keeping separation; order: try removing anchors with SMALL max entry first
(so the survivors show which large-scale anchors are needed), or reverse.  Usage: twin_wext.py m R k [rev]"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import eval_germ, orbit
from twin_wbar import anchors, ufeat
from twin_extract import minimal, solve
import sym_md
m, R, k = map(int, sys.argv[1:4]); rev = len(sys.argv) > 4
sym_md.MODE['pred'] = sym_md.twin_leaves
fam = sym_md.family(m, R)
reps = anchors(m, k)
A = np.array([ufeat(m, reps, lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam]).T
b = np.array(ufeat(m, reps, lambda Z: Z.max(axis=1)))
order = sorted(range(len(reps)), key=lambda i: (max(reps[i]), sum(reps[i])), reverse=not rev)
idx = minimal(A, b, order)
c = solve(A, b, idx)
print(f'm={m} R={R} k={k}: support {len(idx)} orbits')
for i, ci in sorted(zip(idx, c), key=lambda t: reps[t[0]]):
    print('  ', reps[i], ci, 'orbit', len(orbit(reps[i])))
