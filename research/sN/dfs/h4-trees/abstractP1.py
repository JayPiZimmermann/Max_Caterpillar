#!/usr/bin/env python3
"""Abstract component inequality under property P1 (branch h4-trees).

P1: kappa_o >= deg_F(o) - 1 for every vertex (holds for every face of every
pyramid over e_r - e_a + sum_{tree edges} [0, e_parent - e_child], i.e. class pc,
which contains the caterpillar family).
For a tree component C (all edges hinges) with integer kappa:
   D(C) = sum_C kappa - (|C| - 1),
   G_C(x) = sum_{S subset C, (s)} q_C(S) x^{|S|}.
Claim tested: G_C(x) x^{D(C)} <= 1  (then prod_C G_C <= x^{-sum D} = 1 and
w_m <= x^{-m}).  Enumerates free trees on n vertices, kappa_o in
[deg-1, deg+extra].  Uses the C counter ./wfast for q_C(S) counts.
Usage: python abstractP1.py n extra x_num x_den"""
import sys, itertools, subprocess
from fractions import Fraction
from math import factorial
import treeclass as tc
from classW_fast import free_trees
n = int(sys.argv[1]); extra = int(sys.argv[2]); x = Fraction(int(sys.argv[3]), int(sys.argv[4]))
vs = list(range(n))
lines = []; meta = []
for edges in free_trees(vs) if n > 1 else [[]]:
    nbr = [0] * n; deg = [0] * n
    for u, w in edges:
        nbr[u] |= 1 << w; nbr[w] |= 1 << u; deg[u] += 1; deg[w] += 1
    for kap in itertools.product(*[range(deg[v] - 1, deg[v] + extra + 1) for v in vs]):
        lines.append(f'{n} ' + ' '.join(map(str, nbr)) + ' ' + ' '.join(map(str, kap)) + '\n')
        meta.append((edges, kap))
out = subprocess.run(['./wfast'], input=''.join(lines), capture_output=True, text=True, check=True).stdout.split('\n')
best = None
for (edges, kap), line in zip(meta, out):
    c = list(map(int, line.split()))
    G = sum(Fraction(c[s], factorial(n - s)) * x ** s for s in range(n + 1))
    D = sum(kap) - (n - 1)
    val = G * x ** D
    if best is None or val > best[0]:
        best = (val, edges, kap, D, G)
v, e, k, D, G = best
print(f'n={n} extra={extra} x={x}: max G*x^D = {v} = {float(v):.5f} at edges={e} kappa={k} D={D} G={G}')
