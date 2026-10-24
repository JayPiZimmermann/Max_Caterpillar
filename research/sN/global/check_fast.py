#!/usr/bin/env python3
"""Per-unit cross-check of mixed_fast.unit_weight against direct evaluation of
the full unit at every locality cube (integers, B = 10^3, delta = 10^-6).
Usage: python3 check_fast.py N m [sample]"""
import itertools, math, random, sys
from fractions import Fraction
N, m = int(sys.argv[1]), int(sys.argv[2])
sample = int(sys.argv[3]) if len(sys.argv) > 3 else 0
sys.argv = ['x', str(N), str(m)]
import mixed_fast as mf


def relu(t):
    return t if t > 0 else 0


def brute(edges, last, states):
    lin = [e for e, s in zip(edges, states) if s == 1]
    hin = [e for e, s in zip(edges, states) if s == 2]
    W = Fraction(0)
    B, big = 10 ** 3, 10 ** 6
    for T in itertools.combinations(range(N), m):
        rest = [o for o in range(N) if o not in T]
        for order in itertools.permutations(rest):
            pos = [0] * N
            for k, o in enumerate(order):
                pos[o] = -B ** (k + 1) * big
            tot = 0
            for sz in range(m + 1):
                for SS in itertools.combinations(T, sz):
                    y = list(pos)
                    for t in SS:
                        y[t] += 1
                    A = y[last] - y[0] + sum(y[p] - y[c] for p, c in lin) + \
                        sum(relu(y[p] - y[c]) for p, c in hin)
                    tot += (-1) ** (m - sz) * relu(A)
            if tot:
                W += Fraction(1, math.factorial(N - m))
    return W


r = N - 2
allunits = [(S, st) for size in range(1, r + 1) for S in itertools.combinations(range(1, r + 1), size)
            for st in itertools.product(range(3), repeat=r)]
if sample:
    random.seed(1)
    allunits = random.sample(allunits, sample)
bad = 0
for S, st in allunits:
    edges, last = mf.caterpillar(S)
    a = mf.unit_weight(edges, last, st)[0]
    b = brute(edges, last, st)
    if a != b:
        bad += 1
        print('MISMATCH', S, st, a, b)
print(f'N={N} m={m}: checked {len(allunits)} units, mismatches {bad}')
