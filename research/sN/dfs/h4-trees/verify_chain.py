#!/usr/bin/env python3
"""Per-instance control of the proof chain (branch h4-trees):
for every free tree C on n vertices and every e in {0..emax}^n (kappa = deg-1+e):
   exact G_C(1/2) * (1/2)^D   <=   F_DP(C, e)  (V2 tree DP, rooted at a max-degree vertex)   <= 1,
where G_C is computed by the C counter (direct definition: conditions (a),(s)).
Usage: python verify_chain.py n emax"""
import sys, itertools, subprocess
from fractions import Fraction
from math import factorial
from classW_fast import free_trees
from dpV2 import eval_tree, final
n = int(sys.argv[1]); emax = int(sys.argv[2]); x = Fraction(1, 2)
lines, meta = [], []
for edges in (free_trees(list(range(n))) if n > 1 else [[]]):
    adj = {v: [] for v in range(n)}
    for u, w in edges: adj[u].append(w); adj[w].append(u)
    nbr = [sum(1 << w for w in adj[v]) for v in range(n)]
    for e in itertools.product(range(emax + 1), repeat=n):
        kap = [len(adj[v]) - 1 + e[v] for v in range(n)]
        lines.append(f'{n} ' + ' '.join(map(str, nbr)) + ' ' + ' '.join(map(str, kap)) + '\n')
        meta.append((adj, e, kap))
out = subprocess.run(['./wfast'], input=''.join(lines), capture_output=True, text=True, check=True).stdout.split('\n')
viol1 = viol2 = 0; worst = Fraction(0); cnt = 0
for (adj, e, kap), line in zip(meta, out):
    c = list(map(int, line.split()))
    G = sum(Fraction(c[s], factorial(n - s)) * x ** s for s in range(n + 1))
    D = sum(kap) - (n - 1)
    lhs = G * x ** D
    if n >= 3:
        root = max(range(n), key=lambda v: len(adj[v]))
        F = final(eval_tree(adj, e, root))
        if lhs > F: viol1 += 1
        if F > 1: viol2 += 1
    else:
        F = lhs
        if F > 1: viol2 += 1
    worst = max(worst, lhs); cnt += 1
print(f'n={n} emax={emax}: {cnt} instances; exact>DP violations {viol1}; DP>1 violations {viol2}; max exact G x^D = {worst}')
