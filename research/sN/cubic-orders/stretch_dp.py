#!/usr/bin/env python3
"""Exact max over leaf patterns of the edge-type stretch sum, by DP (k <= 60),
plus the charging bound max(1, n/2) * 2^n / n! (n = k-1) used in the Lean proof
(MaxCaterpillar/CountCubic/StretchSum.lean). Independent of stretch_sum.py:
DP over pattern classes {0: leafless, 1: one leaf, 2: other} instead of
enumeration."""
from fractions import Fraction as F
from math import factorial as f
def leaf(k, j): return F(1, f(j-1)*f(k-j))
def spine(k, j): return F(1, f(j-1)*f(k-j-1))
for k in range(1, 61):
    best = {}  # class of s_j -> max partial sum
    for j in range(1, k+1):
        new = {}
        for cj in (0, 1, 2):
            gain = leaf(k, j) if cj == 1 else F(0)
            if j == 1:
                new[cj] = gain
            else:
                new[cj] = max(best[cp] + gain + (spine(k, j-1) if cp == 0 and cj == 0 else 0)
                              for cp in (0, 1, 2))
        best = new
    m = max(best.values()); n = k-1
    charge = max(F(1), F(n, 2)) * F(2**n, f(n))
    assert m <= charge <= 2, (k, m, charge)
    if k <= 8: print(k, m, charge)
print("ok: max <= charging bound <= 2 for k = 1..60")
