#!/usr/bin/env python3
"""Exhaustive check of sum_T p_T <= 2 under property P for N = 6.

All forests on vertices 1..N-1 (apex 0 isolated, kappa_0 = -1), all kappa with
-1 <= kappa_o <= deg(o) + 1 and sum kappa = |F|; P: every vertex has at most two
F-neighbours with kappa >= 1.
"""
import itertools, sys
from fractions import Fraction
N = int(sys.argv[1])
exec(open('research/sN/abstract_test.py').read().split('worst = 0')[0].replace('N = int(sys.argv[1]); trials = int(sys.argv[2]); seed = int(sys.argv[3])', '').replace('rng = random.Random(seed)', ''))
V = list(range(1, N))
pairs = list(itertools.combinations(V, 2))
def is_forest(E):
    parent = {v: v for v in V}
    def f(x):
        while parent[x] != x: x = parent[x]
        return x
    for u, w in E:
        a, b = f(u), f(w)
        if a == b: return False
        parent[a] = b
    return True
worst = Fraction(0); cnt = 0
for m in range(0, N - 1):
    for E in itertools.combinations(pairs, m):
        if not is_forest(E): continue
        F = set(E)
        deg = {v: 0 for v in V}
        for u, w in F: deg[u] += 1; deg[w] += 1
        for kv in itertools.product(*[range(-1, deg[v] + 2) for v in V]):
            if sum(kv) - 1 != len(F): continue
            kappa = [-1] + list(kv)
            if any(sum(1 for (x, y) in F for z in ((y,) if x == v else (x,) if y == v else ()) if kappa[z] >= 1) > 2 for v in V):
                continue
            cnt += 1
            t = valid_count(F, kappa)
            if t > worst:
                worst = t; print('new worst', t, sorted(F), kappa, flush=True)
print('checked', cnt, 'worst', worst)
