#!/usr/bin/env python3
"""Abstract test of Claim W (general-tree per-unit bound).
Forest F on V' = {0..n-1} (the non-apex labels), integers kappa with sum = |F| + 1.
For a top set T' (|T'| = j) count orders of O = V' \\ T' such that every o in O has exactly kappa_o
F-neighbours above it (in T' or earlier), and (s): every t in T' without F-neighbour in T' has kappa_t != 0.
Claim W: sum_{T'} #valid orders <= C(n-1, j-1) (n-j)!   for all 1 <= j <= n.
Enumerates all labelled forests on n vertices and all kappa in [lo, deg+hi]; reports max ratio.
Usage: claimW_graphs.py n lo hi  (all simple graphs, not only forests)"""
import sys, itertools, math
from functools import lru_cache
n, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
allE = list(itertools.combinations(range(n), 2))
def is_forest(E):
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for u, v in E:
        a, b = f(u), f(v)
        if a == b: return False
        par[a] = b
    return True
forests = [E for r in range(len(allE) + 1) for E in itertools.combinations(allE, r)]  # ALL graphs
best = {j: (0, None) for j in range(1, n + 1)}
nf = 0
for E in forests:
    nb = [0] * n
    for u, v in E: nb[u] |= 1 << v; nb[v] |= 1 << u
    deg = [bin(x).count('1') for x in nb]
    ranges = [range(lo, deg[o] + hi + 1) for o in range(n)]
    for kap in itertools.product(*ranges):
        if sum(kap) != len(E) + 1: continue
        nf += 1
        @lru_cache(None)
        def g(R):  # R = set placed (bitmask, includes T'); number of ways to complete
            if R == (1 << n) - 1: return 1
            tot = 0
            for o in range(n):
                if not R >> o & 1 and bin(nb[o] & R).count('1') == kap[o]:
                    tot += g(R | 1 << o)
            return tot
        for j in range(1, n + 1):
            s = 0
            for T in itertools.combinations(range(n), j):
                Tm = sum(1 << t for t in T)
                if any(nb[t] & Tm == 0 and kap[t] == 0 for t in T): continue
                s += g(Tm)
            r = s / (math.comb(n - 1, j - 1) * math.factorial(n - j))
            if r > best[j][0]: best[j] = (r, (E, kap, s))
print(f'n={n} kappa in [{lo}, deg+{hi}]: {nf} (forest,kappa) instances')
for j in range(1, n + 1):
    print(f'  j={j}: max sum/(C(n-1,j-1)(n-j)!) = {best[j][0]:.4f}  at {best[j][1]}')
