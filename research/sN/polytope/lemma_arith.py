#!/usr/bin/env python3
"""Exact arithmetic of the proof of Q_C(1/4) <= 1 (research/sN/polytope/lemma_arith.py)
and the resulting bound s_N >= max_{3<=m<=N} C(N,m) 4^{-m}."""
from fractions import Fraction as F
from math import factorial as fa, comb, e

r = F(1, 4)
rho = lambda n: max(F(1, n * fa(m - 1) * fa(n - m)) for m in range(1, n + 1))
print('rho_1..6 =', [str(rho(n)) for n in range(1, 7)])
assert all(rho(n) <= F(2 ** (n - 1), fa(n)) for n in range(1, 30))
tail = F(1, 3) * F(5, 3)          # sum_{n>=4} 2^{n-1}/n! <= (8/24) sum (2/5)^k
assert all(F(2 ** n, fa(n + 1)) <= F(2, 5) * F(2 ** (n - 1), fa(n)) for n in range(4, 40))
Srho = F(11, 6) + tail
print('sum rho <=', Srho, float(Srho)); assert Srho <= F(12, 5)
SR = F(12, 5)
# Lemma A: A_1 <= 1/2, A_L <= r/2 + r^2 SR + r/2 for L >= 2
A1 = r + r * 1
AL = r / 2 + r * r * SR + r * F(1, 2)
print('A_1 =', A1, ' A_L(L>=2) <=', AL, float(AL)); assert A1 <= F(1, 2) and AL <= F(1, 2)
# root cases
c1 = r * r
c2 = {1: r, 2: r * 1 + F(1, 2), 3: r * 1 + F(1, 8) * (SR - 1) + r * F(1, 2) + F(1, 3)}
sum_inv_fact2 = F(1, 2) + F(1, 6) + F(1, 24) + F(1, 120) * F(6, 5)   # sum_{n>=2} 1/n! <= this
assert sum_inv_fact2 >= F(int((e - 2) * 10**6), 10**6)
c3 = {1: r + F(1, 2), 2: r * F(1, 2) + r + F(1, 2), 3: r * F(1, 2) + r * F(1, 2) + r * sum_inv_fact2 + F(1, 6)}
for name, val in [('lam1>=1', c1)] + [(f'lam1=-1 L{"=" if k<3 else ">="}{k}', v) for k, v in c2.items()] + \
        [(f'lam1=0 L{"=" if k<3 else ">="}{k}', v) for k, v in c3.items()]:
    print(f'  {name}: Q <= {val} = {float(val):.4f}'); assert val <= 1
# bounds
for N in [6, 10, 20, 30, 40, 50, 60, 80, 100, 200]:
    b = max(F(comb(N, m), 4 ** m) for m in range(3, N + 1))
    mstar = max(range(3, N + 1), key=lambda m: F(comb(N, m), 4 ** m))
    print(f'N={N}: max_m C(N,m)/4^m = {float(b):.4g} (m={mstar});  cubic C(N,3)/2 = {comb(N,3)/2:.4g}; (5/4)^N/(N+1) = {1.25**N/(N+1):.4g}')
