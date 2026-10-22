#!/usr/bin/env python3
"""F(L) = sum_{A subset [L]} x^|A| prod_{maximal runs of [L]\\A of length n} 2^(-floor(n/2)).
If max_{L>=2} F(L) <= 1, the component inequality E3 holds with this x (spine
matching bound), giving s_N >= C(N,k) x^k for all k >= 3."""
from fractions import Fraction
import sys
def F(L, x):
    # DP over positions: state = current run length parity info -> track run length
    # weight of a run of length n: 2^-(n//2); accumulate per position
    # states: (in_run_length) ; we multiply 1/2 whenever run length becomes even
    dp = {0: Fraction(1)}           # key: current run length (0 = last was in A or start)
    for _ in range(L):
        new = {}
        for n, w in dp.items():
            new[0] = new.get(0, 0) + w * x                    # put vertex in A
            m = n + 1
            f = Fraction(1, 2) if m % 2 == 0 else Fraction(1)
            new[m] = new.get(m, 0) + w * f                   # outside, extends run
        dp = new
    return sum(dp.values())
for x in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 5), Fraction(1, 6), Fraction(1, 8)]:
    vals = [F(L, x) for L in range(1, 61)]
    print(x, 'max_{L>=2} F =', float(max(vals[1:])), 'at L =', 2 + vals[1:].index(max(vals[1:])), ' F(60) =', float(vals[-1]))
