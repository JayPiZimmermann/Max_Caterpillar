#!/usr/bin/env python3
"""Abstract test of the component inequality G_C(x) <= 1 (main-session branch).

Tree C on vertices 0..m-1, integer kappa (range -1..deg+1),
G(x) = sum over S subset C with [every t in S has a neighbour in S or kappa_t != 0]
       of q(S) x^|S|,
q(S) = Pr[uniform random order of C \\ S has every vertex o with exactly kappa_o
       neighbours above it (S counts as above)].
Reports max G(x) over all labelled trees on m vertices (Pruefer codes) and all kappa.
Usage: python3 abstract_G.py m x_num x_den
"""
import itertools, math, sys
from fractions import Fraction
m = int(sys.argv[1]); x = Fraction(int(sys.argv[2]), int(sys.argv[3]))


def pruefer_trees(n):
    if n == 1:
        yield []
        return
    if n == 2:
        yield [(0, 1)]
        return
    for code in itertools.product(range(n), repeat=n - 2):
        deg = [1] * n
        for c in code: deg[c] += 1
        edges = []
        code = list(code)
        for c in code:
            leaf = min(i for i in range(n) if deg[i] == 1)
            edges.append((leaf, c)); deg[leaf] -= 1; deg[c] -= 1
        u, w = [i for i in range(n) if deg[i] == 1]
        edges.append((u, w))
        yield edges


def q(S, nbr, kappa):
    rest = [o for o in range(m) if o not in S]
    if any(kappa[o] < 0 or kappa[o] > len(nbr[o]) for o in rest): return Fraction(0)
    idx = {o: i for i, o in enumerate(rest)}
    count = {0: 1}
    for _ in range(len(rest)):
        new = {}
        for placed, cnt in count.items():
            for o in rest:
                b = 1 << idx[o]
                if placed & b: continue
                above = sum(1 for u in nbr[o] if u in S or placed & (1 << idx[u]))
                if above == kappa[o]: new[placed | b] = new.get(placed | b, 0) + cnt
        count = new
    return Fraction(sum(count.values()), math.factorial(len(rest)))


best = Fraction(0); arg = None; seen = set()
for edges in pruefer_trees(m):
    key = tuple(sorted(tuple(sorted(e)) for e in edges))
    if key in seen: continue
    seen.add(key)
    nbr = [[] for _ in range(m)]
    for u, w in edges: nbr[u].append(w); nbr[w].append(u)
    for kappa in itertools.product(*[range(-1, len(nbr[v]) + 2) for v in range(m)]):
        G = Fraction(0)
        for size in range(0, m + 1):
            for S in itertools.combinations(range(m), size):
                Ss = set(S)
                if any(not (set(nbr[t]) & Ss) and kappa[t] == 0 for t in S): continue
                G += q(Ss, nbr, kappa) * x ** size
        if G > best:
            best, arg = G, (edges, kappa)
print(f'm={m} x={x}: max G = {best} = {float(best):.4f} at {arg}', flush=True)
