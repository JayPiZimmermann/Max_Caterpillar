#!/usr/bin/env python3
"""Does sum_T p_T <= 2 hold for an arbitrary forest F with integer weights kappa?

Vertices 0..N-1, apex 0 isolated with kappa_0 = -1, sum kappa = |F|.
A locality (T, order) is valid if T = {0,u,w}, every o outside T has exactly
kappa_o F-neighbours above it, and (b'): uw in F, or v_T = (-1, v_u, v_w) is not a
root multiple, where v_t = kappa_t - #{F-neighbours of t inside T}... (for the
abstract test we use v_t = kappa_t - [uw in F] as the symmetric version).
"""
import itertools, math, random, sys
from fractions import Fraction
N = int(sys.argv[1]); trials = int(sys.argv[2]); seed = int(sys.argv[3])
rng = random.Random(seed)
def valid_count(F, kappa):
    nbr = [[] for _ in range(N)]
    for u, w in F: nbr[u].append(w); nbr[w].append(u)
    tot = Fraction(0)
    for u, w in itertools.combinations(range(1, N), 2):
        T = {0, u, w}; e = (min(u, w), max(u, w)) in F
        if kappa[u] + kappa[w] != e + 1: continue
        if not e:
            if 0 in (kappa[u], kappa[w]) or 1 in (kappa[u], kappa[w]): continue
        rest = [o for o in range(N) if o not in T]
        if any(not 0 <= kappa[o] <= len(nbr[o]) for o in rest): continue
        idx = {o: k for k, o in enumerate(rest)}
        count = {0: 1}
        for _ in range(len(rest)):
            new = {}
            for placed, c in count.items():
                for o in rest:
                    b = 1 << idx[o]
                    if placed & b: continue
                    above = sum(1 for x in nbr[o] if x in T or placed & (1 << idx[x]))
                    if above == kappa[o]: new[placed | b] = new.get(placed | b, 0) + c
            count = new
        tot += Fraction(sum(count.values()), math.factorial(len(rest)))
    return tot
worst = 0
for _ in range(trials):
    verts = list(range(1, N)); rng.shuffle(verts)
    F = set()
    for i in range(1, len(verts)):
        if rng.random() < 0.7:
            F.add(tuple(sorted((verts[i], verts[rng.randrange(i)]))))
    deg = [0] * N
    for u, w in F: deg[u] += 1; deg[w] += 1
    # random kappa with sum |F| + 1 over 1..N-1, entries in [-1, deg]
    for _ in range(20):
        kappa = [-1] + [rng.randint(-1, deg[o] + 1) for o in range(1, N)]
        if sum(kappa) == len(F): break
    else: continue
    nbr2 = [[] for _ in range(N)]
    for u, w in F: nbr2[u].append(w); nbr2[w].append(u)
    if any(sum(1 for x in nbr2[v] if kappa[x] >= 1) > 2 for v in range(N)): continue
    t = valid_count(F, kappa)
    if t > worst:
        worst = t; print('new worst', t, sorted(F), kappa, flush=True)
print('worst', worst)
