#!/usr/bin/env python3
"""Coordinate-flag invariants tau_sigma (iterated face jumps along deletion orders, flag_test.py)
for germs with >= 2 out-leaves at a common centre.  Is max_m outside their span?
Usage: twoleaf_flag.py m R"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from flag_test import tau, orders
from sym_md import family
from pn_test import rank_mod_p

def polytope(m, v, F):
    gens = []
    for i, j in F:            # term relu(z_i - z_j): generator e_i - e_j
        g = [0] * m; g[i] += 1; g[j] -= 1; gens.append(g)
    pts = {tuple([0] * m)}
    for S in itertools.product([0, 1], repeat=len(gens)):
        p = list(v)
        for s, g in zip(S, gens):
            if s: p = [x + y for x, y in zip(p, g)]
        pts.add(tuple(p))
    return list(pts)

m, R = int(sys.argv[1]), int(sys.argv[2])
fam = family(m, R)
ords = orders(m)
# symmetric: use all permutations of each rep (apex 0) -> tau vectors over all orders
cols = []
for v, F in fam:
    for perm in itertools.permutations(range(m)):
        vv = [0] * m
        for t in range(m): vv[perm[t]] = v[t]
        FF = [(perm[i], perm[j]) for i, j in F]
        G = polytope(m, vv, FF)
        cols.append([tau(G, o, list(range(m))) for o in ords])
A = np.array(cols, dtype=np.int64).T
b = np.ones((len(ords), 1), dtype=np.int64)
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b], axis=1))
print(f'm={m} R={R}: {len(fam)} reps, {A.shape[1]} germs, {len(ords)} deletion flags; rank {r1}, with max {r2} -> {"SEPARATED" if r2 > r1 else "not separated"}', flush=True)
