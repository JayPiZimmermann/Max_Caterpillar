#!/usr/bin/env python3
"""Crude local relaxation V2 (branch h4-trees): q'(S) = 2^{-#internal heap vertices}
(v in O is internal iff it has an O-neighbour other than its unique lower one).
R2(C) = sum_S x^{|S| + sum_S e + c(S) - 1} q'(S).  Report max over trees, e in [0,emax].
Usage: python relaxV2.py n emax x_num x_den"""
import sys, itertools
from fractions import Fraction
from classW_fast import free_trees
from comps_util import comps
n = int(sys.argv[1]); emax = int(sys.argv[2]); x = Fraction(int(sys.argv[3]), int(sys.argv[4]))
worst = Fraction(0); arg = None
for edges in (free_trees(list(range(n))) if n > 1 else [[]]):
    adj = {v: [] for v in range(n)}
    for u, w in edges: adj[u].append(w); adj[w].append(u)
    deg = [len(adj[v]) for v in range(n)]
    for e in itertools.product(range(emax + 1), repeat=n):
        kap = [deg[v] - 1 + e[v] for v in range(n)]
        R = Fraction(0)
        for mask in range(1 << n):
            S = {v for v in range(n) if mask >> v & 1}
            if any(not (set(adj[t]) & S) and kap[t] == 0 for t in S): continue
            O = [v for v in range(n) if v not in S]
            Ks = comps(O, adj)
            if any(sum(1 for v in K if e[v] == 1) != 1 or any(e[v] > 1 for v in K) for K in Ks): continue
            internal = sum(1 for v in O if sum(1 for w in adj[v] if w not in S) - (1 - e[v]) >= 1)
            R += x ** (len(S) + sum(e[v] for v in S) + len(Ks) - 1) * Fraction(1, 2 ** internal)
        if R > worst: worst = R; arg = (edges, e)
print(f'n={n} emax={emax} x={x}: max R2 = {worst} = {float(worst):.4f} at {arg}')
