"""Symmetric (S_m on the non-centre vertices) family:
 neuron(p,q,r; theta) = sigma(g0 + sum_{o in theta} sigma(x_a - x_o)),
 g0 = p*sum_o (x_a-x_o) + q*sum_{o<o'} (x_a - min(x_o,x_o')) + r*sum_o sigma(x_a - x_o).
Weights depend on (p,q,r,|theta|).  Test: braid-PL (n representative chambers: centre at each
position) and top != 0 (top computed exactly via T = sum_S (-1)^{|S|+1} sigma(g(1_S)), summed over orbit).
python gadget_lp.py m D Rmax"""
import sys, itertools
import numpy as np
from fractions import Fraction as Fr
from math import comb
from modp import rank_mod, P as PR
m = int(sys.argv[1]); D = int(sys.argv[2]); RM = int(sys.argv[3]); TV = [int(v) for v in sys.argv[4].split(",")]
n = m + 1
grid = [Fr(k, D) for k in range(-RM * D, RM * D + 1)]
params = [(p, q, r) for p in grid for q in grid for r in grid]
def g_lin(p, q, r, theta, order):
    """linear coefficient vector (by element) of g on chamber 'order' (list of elements top first); a=0."""
    pos = {e: i for i, e in enumerate(order)}
    a = [Fr(0)] * n
    others = range(1, n)
    for o in others:
        a[0] += p; a[o] -= p
        if pos[0] < pos[o]:   # sigma(x_a - x_o) active
            w = r + theta.get(o, 0)
            a[0] += w; a[o] -= w

    for o, o2 in itertools.combinations(others, 2):
        lo = o if pos[o] > pos[o2] else o2      # min(x_o,x_o') = lower element
        a[0] += q; a[lo] -= q
    return a
def val_S(p, q, r, theta, S):
    v = Fr(0)
    xa = 1 if 0 in S else 0
    for o in range(1, n):
        xo = 1 if o in S else 0
        v += p * (xa - xo) + (r + theta.get(o, 0)) * max(xa - xo, 0)
    for o, o2 in itertools.combinations(range(1, n), 2):
        v += q * (xa - min(1 if o in S else 0, 1 if o2 in S else 0))
    return v
types = {}; cross = {}; top = {}
subsets = [set(S) for k in range(n + 1) for S in itertools.combinations(range(n), k)]
for (p, q, r) in params:
    for tv in itertools.product(TV, repeat=m):
        theta = {o: t for o, t in zip(range(1, n), tv) if t}; k = tuple(sorted(tv))
        var = types.setdefault((p, q, r, k), len(types))
        # top contribution of this neuron (orbit sum = sum over all theta of size k, we enumerate all)
        T = sum((-1) ** (len(S) + 1) * max(val_S(p, q, r, theta, S), 0) for S in subsets)
        if T: top[var] = top.get(var, 0) + T
        for ca in range(n):   # centre position
            others = list(range(1, n))
            order = others[:ca] + [0] + others[ca:]
            a = g_lin(p, q, r, theta, order)
            assert sum(a) == 0
            Dv = []; s = Fr(0)
            for i in range(n - 1): s += a[order[i]]; Dv.append(s)
            if any(d > 0 for d in Dv) and any(d < 0 for d in Dv):
                first = next(d for d in Dv if d)
                key = (ca,) + tuple(d / abs(first) for d in Dv)
                if first < 0: key = (ca,) + tuple(-d / abs(first) for d in Dv)
                e = cross.setdefault(key, {}); e[var] = e.get(var, 0) + abs(first)
nv = len(types)
def modp(fr): return (fr.numerator % PR) * pow(fr.denominator % PR, PR - 2, PR) % PR
C = np.zeros((len(cross), nv), dtype=np.int64)
for i, e in enumerate(cross.values()):
    for v, c in e.items(): C[i, v] = modp(Fr(c))
L = np.zeros((1, nv), dtype=np.int64)
for v, c in top.items(): L[0, v] = modp(Fr(c))
r1 = rank_mod(C) if len(cross) else 0; r2 = rank_mod(np.vstack([C, L]))
print('m', m, 'grid', len(grid), 'types', nv, 'cross', len(cross), 'TOP', r2 > r1, flush=True)
