#!/usr/bin/env python3
"""Generalized localities: ordered set partition (B_1 > B_2 > ... ) of the labels, block i at height
-K*B^(i-1) (block 1 at 0), and a difference set D (|D| >= 3).  Delta_D = mixed difference over D at the
base point (exact integers).  Reports the tests on which max_N - f_N is nonzero (f_N from fN_tests)."""
import sys, itertools
import loctests as L
from fN_tests import fkeys
def ordered_partitions(s):
    s = list(s)
    if not s: yield []; return
    for r in range(1, len(s) + 1):
        for first in itertools.combinations(s, r):
            rest = [x for x in s if x not in first]
            for p in ordered_partitions(rest): yield [first] + p
def val(fun, N, blocks, D, K):
    p = [0] * N
    for i, b in enumerate(blocks):
        for o in b: p[o] = -K * (K ** i) if i else 0
    tot = 0
    for bits in range(1 << len(D)):
        x = list(p)
        for i, t in enumerate(D):
            if bits >> i & 1: x[t] += 1
        tot += (-1) ** (len(D) - bin(bits).count('1')) * fun(x)
    return tot
N = int(sys.argv[1]); ks = fkeys(N); K = 40 * N
f = lambda x: sum(max(0, L.A(k, x)) for k in ks)
mx = lambda x: max(x)
nz = tot = 0; ex = []
for blocks in ordered_partitions(range(N)):
    for r in range(3, N + 1):
        for D in itertools.combinations(range(N), r):
            tot += 1
            v = val(mx, N, blocks, D, K) - val(f, N, blocks, D, K)
            if v: nz += 1; ex.append((blocks, D, v))
print(f'N={N}: generalized tests {tot}, nonzero on max-f_N: {nz}')
for e in ex[:8]: print('  ', e)
