#!/usr/bin/env python3
"""Exact closure check for e=0 parents with arbitrarily many children (h4-trees).

Partial state after k children: z = (A, S, B, X, Y) = (prod alpha, prod sigma,
prod a, sum_k gamma_k prod_{j!=k} sigma_j, sum_k gamma_k prod_{j!=k} a_j), a = sigma+omega.
Update with child (alpha, sigma, a, gamma) in P:
   (A alpha, S sigma, B a, X sigma + gamma S, Y a + gamma B).
Goal: F = A + (X + Y)/2 <= 1 for every k >= 2.
Method: Q2 := conv{states with k = 2..K from vertices of P}; H-representation by
scipy (floats), rationalised; then EXACT checks (Fractions): (i) every generated
state satisfies every facet, (ii) update(vertex of Q2, vertex of P) satisfies
every facet (so Q2 is closed: the update is bilinear), (iii) F <= 1 on Q2's
generating points.  If (i)-(iii) pass, F <= 1 for all k >= 2 children in P."""
import itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.spatial import ConvexHull

# vertices of P as (alpha, sigma, a, gamma); P from closure_test (sigma,gamma,omega,alpha)
Pv_sgwa = [(0,0,0,0),(0,0,0,1),(0,0,1,0),(0,0,1,1),(0,1,0,0),(0,1,0,Fr(1,2)),(Fr(1,3),Fr(2,3),0,Fr(2,3)),(1,0,0,0)]
PV = [(Fr(a), Fr(s), Fr(s) + Fr(w), Fr(g)) for (s, g, w, a) in Pv_sgwa]

def upd(z, c):
    A, S, B, X, Y = z; al, si, a, ga = c
    return (A * al, S * si, B * a, X * si + ga * S, Y * a + ga * B)

start = (Fr(1), Fr(1), Fr(1), Fr(0), Fr(0))
lvl = {start}
pts = set()
for k in range(1, 5):
    lvl = {upd(z, c) for z in lvl for c in PV}
    if k >= 2: pts |= lvl
pts = sorted(pts)
print(len(pts), 'states (k=2..4)')
Fmax = max(z[0] + (z[3] + z[4]) / 2 for z in pts)
print('max F on states:', Fmax)
M = np.array([[float(t) for t in z] for z in pts])
hull = ConvexHull(M)
verts = [pts[i] for i in hull.vertices]
print(len(verts), 'hull vertices')
# facets: normal.x + offset <= 0
facets = []
for eq in hull.equations:
    nrm = eq[:-1]; off = eq[-1]
    # rationalise by scaling to the largest abs coefficient
    sc = max(abs(nrm).max(), abs(off))
    nr = [Fr(t / sc).limit_denominator(1000) for t in nrm]; of = Fr(off / sc).limit_denominator(1000)
    facets.append((tuple(nr), of))
facets = sorted(set(facets))
print(len(facets), 'distinct rationalised facets')
def ok(z):
    return all(sum(n * t for n, t in zip(nr, z)) + of <= 0 for nr, of in facets)
bad_i = [z for z in pts if not ok(z)]
print('(i) generated states outside rationalised hull:', len(bad_i))
bad_ii = [(z, c) for z in verts for c in PV if not ok(upd(z, c))]
print('(ii) updates of hull vertices leaving the hull:', len(bad_ii))
print('(iii) max F on hull vertices:', max(z[0] + (z[3] + z[4]) / 2 for z in verts))
for nr, of in facets: print('   ', [str(t) for t in nr], '<=', str(-of))
