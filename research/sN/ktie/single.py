#!/usr/bin/env python3
"""Is max_k congruent to c * (one local unit) modulo functions missing a coordinate?

f ~ 0 modulo sums of functions each independent of one coordinate iff every
k-fold mixed difference D f(b, h) = sum_S (-1)^{k-|S|} f(b + h 1_S) (h_i > 0
per coordinate) vanishes.  We sample integer boxes (b, h) and test
D max_k = c * D g exactly.  A failure on the sample is a rigorous proof that
g does not work (the sample constraints are a subset of the true ones).
Vocabulary: v in [-V, V]^k with sum 0, M any set of pairs i<j (superset of
the local vocabulary for these bounds).
Usage: python3 single.py k V
"""
import itertools, random, sys
from fractions import Fraction
k, V = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(7)
def relu(t): return t if t > 0 else 0
boxes = [(tuple(rng.randint(-6, 6) for _ in range(k)), tuple(rng.randint(1, 6) for _ in range(k))) for _ in range(400)]
boxes = [((0,) * k, (1,) * k)] + boxes
def D(f, b, hh):
    tot = 0
    for bits in range(1 << k):
        x = [b[i] + (hh[i] if bits >> i & 1 else 0) for i in range(k)]
        tot += (-1) ** (k - bin(bits).count('1')) * f(x)
    return tot
dm = [D(max, b, hh) for b, hh in boxes]
pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
hits = 0
for vv in itertools.product(range(-V, V + 1), repeat=k - 1):
    v = vv + (-sum(vv),)
    if abs(v[-1]) > V: continue
    for mask in range(1 << len(pairs)):
        M = [pairs[t] for t in range(len(pairs)) if mask >> t & 1]
        g = lambda x: relu(sum(a * b for a, b in zip(v, x)) + sum(relu(x[i] - x[j]) for i, j in M))
        d0 = D(g, *boxes[0])
        if d0 == 0: continue
        c = Fraction(dm[0], d0)
        ok = True
        for (b, hh), m in zip(boxes[1:], dm[1:]):
            if c * D(g, b, hh) != m: ok = False; break
        if ok:
            hits += 1; print('MATCH', v, M, c)
print(f'k={k} V={V}: single-unit matches = {hits}')
