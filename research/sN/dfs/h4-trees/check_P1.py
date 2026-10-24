#!/usr/bin/env python3
"""Which units satisfy P1 (kappa_o >= deg_M(o) - 1 for all o) and Sigma h = 0, M a forest?  (h4-trees)
Checks: every caterpillar face key (scripts/vocabulary_search.dictionary) and every pc-class key
for N = 4..6; reports the fraction of class-G keys violating P1."""
import sys
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
import treeclass as tc
from classW_fast import keys

def p1(k):
    h, M = k; N = len(h)
    deg = [0] * N; kap = list(h)
    for i, j in M: deg[i] += 1; deg[j] += 1; kap[i] += 1
    # forest check (union-find)
    par = list(range(N))
    def f(u):
        while par[u] != u: par[u] = par[par[u]]; u = par[u]
        return u
    forest = True
    for i, j in M:
        a, b = f(i), f(j)
        if a == b: forest = False
        par[a] = b
    return sum(h) == 0 and forest and all(kap[o] >= deg[o] - 1 for o in range(N))

for N in (4, 5, 6):
    K0, _ = vs.dictionary(N)
    print(f'N={N}: caterpillar keys {len(K0)}, P1 fails on {sum(1 for k in K0 if not p1(k))}')
    pc = set(keys(N, 'pc')); print(f'      pc keys (apex 0) {len(pc)}, P1 fails on {sum(1 for k in pc if not p1(k))}')
    G = set(keys(N, 'G')); print(f'      G keys (apex 0) {len(G)}, P1 fails on {sum(1 for k in G if not p1(k))}')
