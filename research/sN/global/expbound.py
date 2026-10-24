#!/usr/bin/env python3
"""Evaluate the proved-on-paper bound s_N >= C(N,m) / c_m  (global/expbound.py)

c_m = [x^{m-1}] 1/(1 - 2 A(x)),  A(x) = sum_{j>=1} a_j x^j,
a_j = sum_{k=1}^{j} B^{k+1},  B = sum_l b_l with b_l the run bound:
  'matching': b_l = 2^{-floor(l/2)}  (B = 4, elementary)
  'euler'   : b_l = E_l / l!          (B = sec 1 + tan 1, uses Niven's theorem)
Exact rational arithmetic for 'matching'.
"""
import math
from fractions import Fraction


def coeffs(Bv, M):
    a = [Fraction(0)] + [sum(Bv ** (k + 1) for k in range(1, j + 1)) for j in range(1, M + 1)]
    # g = 1/(1 - 2A): g_0 = 1, g_n = sum_{j=1}^n 2 a_j g_{n-j}
    g = [Fraction(1)]
    for n in range(1, M + 1):
        g.append(sum(2 * a[j] * g[n - j] for j in range(1, n + 1)))
    return g


M = 400
g = coeffs(Fraction(4), M)
print('c_m (matching bound) for m=3..8:', [float(g[m - 1]) for m in range(3, 9)])
print('growth ratio c_{m+1}/c_m at m=300:', float(g[300] / g[299]))
for N in [10, 100, 300, 500, 1000, 2000, 5000]:
    best, bm = 0, None
    for m in range(3, min(N, M) + 1):
        v = Fraction(math.comb(N, m)) / g[m - 1]
        if v > best:
            best, bm = v, m
    cubic = math.comb(N, 3) / 2
    print(f'N={N}: max_m C(N,m)/c_m = {float(best):.4g} at m={bm};  cubic C(N,3)/2 = {cubic:.4g};'
          f'  log(bound)/N = {math.log(float(best)) / N if best > 1 else 0:.4f}')
