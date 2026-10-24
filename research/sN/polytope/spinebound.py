#!/usr/bin/env python3
"""Renewal upper bound for Q_C(r) on spine components (research/sN/polytope/spinebound.py).
rho_n  = max_m 1/(n (m-1)! (n-m)!)          (non-root run, best min position)
A_L, B_L: fresh / forced-X non-root sequences;  R_L: root analysis (see proof).
Prints sup_L R_L for given r (exact Fractions, L <= Lmax)."""
import sys
from fractions import Fraction as F
from math import factorial as fa


def rho(n):
    return max(F(1, n * fa(m - 1) * fa(n - m)) for m in range(1, n + 1))


def rootnonmin(n):
    return max(F(1, n * fa(m - 1) * fa(n - m)) for m in range(2, n + 1))


def bound(r, Lmax=40):
    A, B = [F(1)], [F(1)]
    for L in range(1, Lmax + 1):
        A.append(r * A[L - 1] + sum(r * rho(n) * B[L - n] for n in range(1, L + 1)))
        B.append(r * A[L - 1])
    out = []
    for L in range(1, Lmax + 1):
        # lambda_1 = -1, a_1 = 0 (requires L >= 2)
        c1 = F(0)
        if L >= 2:
            c1 = r * A[L - 2] + sum(rootnonmin(n) * B[L - n] for n in range(2, L + 1))
        # lambda_1 = 0, any a_1 (a_1 >= 1 if L = 1)
        n1 = F(1, 2) if L == 1 else F(1)
        c2 = r * A[L - 1] + n1 * B[L - 1] + sum(F(1, fa(n)) * B[L - n] for n in range(2, L + 1))
        # lambda_1 = -1, a_1 >= 1
        c3 = r * A[L - 1] + (sum(rootnonmin(n) * B[L - n] for n in range(2, L + 1)) if L >= 2 else 0)
        c4 = r * r * A[L - 1]
        out.append(max(c1, c2, c3, c4))
    return max(out), max(A), out


for r in [F(1, 4), F(3, 10), F(1, 3), F(7, 20), F(2, 5)]:
    sup, Amax, out = bound(r)
    print(f'r={r}: sup_L R_L = {float(sup):.5f}, sup A = {float(Amax):.4f}, R_L for L=1..8: {[round(float(x),4) for x in out[:8]]}')
