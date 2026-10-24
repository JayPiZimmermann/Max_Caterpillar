#!/usr/bin/env python3
"""Defect-weighted component bound (research/sN/polytope/defect.py).
D(C) = sum_C kappa - (|C| - 1); sum over all components (isolated vertices
included) is 0, so G_k(r) = prod_C Q_C(r) with Q_C(r) = r^{D(C)} P_C(r).
Reports max_C Q_C(r) and r0(N) = sup{r <= 1: Q_C(r) <= 1 for all C}.
Usage: python3 defect.py N"""
import sys
from fractions import Fraction
import genfun as gf

N = int(sys.argv[1])
keys = set()
for S, states, edges, last in gf.all_units(N):
    kappa, hin = gf.unit_data(N, edges, last, states)
    comps, nbr = gf.components(N, hin)
    for c in comps:
        keys.add(gf.canon(c, nbr, kappa))
polys = {k: gf.comp_poly(k) for k in keys}
D = {k: sum(k[1]) - (k[0] - 1) for k in keys}


def Q(k, r):
    return r ** D[k] * sum(c * r ** i for i, c in enumerate(polys[k]))


for r in [Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(1)]:
    best = max(keys, key=lambda k: Q(k, r))
    print(f'N={N} r={r}: max_C Q_C = {float(Q(best, r)):.5f} at n={best[0]} kappa={best[1]} D={D[best]} E={best[2]} P={[str(c) for c in polys[best]]}')
lo, hi = Fraction(1, 100), Fraction(1)
for _ in range(40):
    mid = (lo + hi) / 2
    if max(Q(k, mid) for k in keys) <= 1:
        lo = mid
    else:
        hi = mid
best = max(keys, key=lambda k: Q(k, hi))
print(f'N={N}: r0 in [{float(lo):.6f},{float(hi):.6f}] binding n={best[0]} kappa={best[1]} D={D[best]} E={best[2]} P={[str(c) for c in polys[best]]}')
print('  D histogram', sorted({d: sum(1 for k in keys if D[k] == d) for d in set(D.values())}.items()))
