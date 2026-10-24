#!/usr/bin/env python3
"""m = 4 twin family: g_k = relu(-z0 + (1-2k) z1 + k(z2+z3) + relu(z2-z1) + relu(z3-z1)), k in [-K,K].
(in-orientation at kappa = out-orientation at kappa-1, so this is the whole twin family at m = 4.)
Usage: twin_m4.py K values"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import SymTests, eval_germ, rank_mod_p
K = int(sys.argv[1]); vals = [int(x) for x in sys.argv[2].split(',')]
m = 4
pats = list(itertools.combinations_with_replacement(vals, m))
T = SymTests(m, pats)
cols = []
for k in range(-K, K + 1):
    v = (-1, 1 - 2 * k, k, k); F = [(2, 1), (3, 1)]
    cols.append(T.vec(lambda Z: eval_germ(v, F, Z)))
A = np.array(cols).T
b = T.vec(lambda Z: Z.max(axis=1))[:, None]
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b], 1))
print(f'K={K} vals={vals}: {len(pats)} tests, rank {r1}, with max {r2}', 'SEP' if r2 > r1 else 'not')
