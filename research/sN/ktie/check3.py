#!/usr/bin/env python3
"""Measured check that max_4 = c1 g1 + c2 g2 + c3 g3 modulo functions missing a
coordinate, for the size-3 solution found by sprime.py (N=7, k=4): solve for the
coefficients exactly on the base boxes, then test 20000 random rational boxes."""
import random
from fractions import Fraction
k = 4
G = [((-1, -1, 1, 1), ((0, 2),)), ((-1, -1, 1, 1), ((0, 2), (0, 3))), ((0, 0, -1, 1), ((0, 3), (1, 3)))]
def relu(t): return t if t > 0 else 0
def ev(key):
    v, M = key
    return lambda x: relu(sum(a * c for a, c in zip(v, x)) + sum(relu(x[i] - x[j]) for i, j in M))
def D(f, b, hh):
    tot = 0
    for bits in range(1 << k):
        x = [b[i] + (hh[i] if bits >> i & 1 else 0) for i in range(k)]
        tot += (-1) ** (k - bin(bits).count('1')) * f(x)
    return tot
fs = [ev(g) for g in G]
rng = random.Random(11)
def box(): return (tuple(Fraction(rng.randint(-40, 40), rng.randint(1, 9)) for _ in range(k)), tuple(Fraction(rng.randint(1, 40), rng.randint(1, 9)) for _ in range(k)))
import itertools
rows = []
while True:
    b = box(); rows.append(([D(f, *b) for f in fs], D(max, *b)))
    if len(rows) >= 3:
        def det3(m): return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0]) + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
        A = [r[0] for r in rows[-3:]]; y = [r[1] for r in rows[-3:]]
        d = det3(A)
        if d != 0:
            c = []
            for j in range(3):
                Aj = [[(y[i] if t == j else A[i][t]) for t in range(3)] for i in range(3)]
                c.append(Fraction(det3(Aj)) / d)
            break
print('coefficients', c)
bad = 0
for _ in range(20000):
    b = box()
    if sum(ci * D(f, *b) for ci, f in zip(c, fs)) != D(max, *b): bad += 1
print('random rational boxes 20000, mismatches', bad)
