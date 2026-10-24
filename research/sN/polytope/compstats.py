#!/usr/bin/env python3
"""Component-level stats (research/sN/polytope/compstats.py): all hinge components
arising in caterpillar units of arity N; max_C P_C(r) and threshold r0(N)
= sup{r : P_C(r) <= 1 for all C}.  Usage: python3 compstats.py N"""
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


def val(p, r):
    return sum(c * r ** i for i, c in enumerate(p))


for r in [Fraction(1, 2), Fraction(2, 3), Fraction(3, 4), Fraction(1)]:
    best = max(polys, key=lambda k: val(polys[k], r))
    print(f'N={N} r={r}: max_C P_C(r) = {float(val(polys[best], r)):.5f}  at n={best[0]} kappa={best[1]} E={best[2]} poly={[str(c) for c in polys[best]]}')
lo, hi = Fraction(0), Fraction(2)
for _ in range(40):
    mid = (lo + hi) / 2
    if max(val(p, mid) for p in polys.values()) <= 1:
        lo = mid
    else:
        hi = mid
best = max(polys, key=lambda k: val(polys[k], hi))
print(f'N={N}: r0 in [{float(lo):.6f}, {float(hi):.6f}], binding component n={best[0]} kappa={best[1]} E={best[2]} poly={[str(c) for c in polys[best]]}')
print(f'  #distinct components {len(keys)}; max P_C(0) = {max(p[0] for p in polys.values())}')
