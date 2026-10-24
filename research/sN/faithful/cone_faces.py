#!/usr/bin/env python3
"""Compare normalizedKeys r with normalizedConeFaceKeys r (NormalizeFaces.lean:
faces of the normalized word cones), both by literal emulation, N given."""
import itertools, sys
sys.path.insert(0, 'research/sN/faithful')
sys.argv = sys.argv[:2]
N = int(sys.argv[1]); r = N - 2; n = r + 1
def vtx(a):
    v = [0] * n
    if a > 0: v[a - 1] = 1
    return tuple(v)
sub = lambda u, v: tuple(x - y for x, y in zip(u, v))
add = lambda u, v: tuple(x + y for x, y in zip(u, v))
parent = lambda S, j: max([0] + [i for i in S if i < j])
diffs = {sub(vtx(a), vtx(b)): (a, b) for a in range(N) for b in range(N) if a != b}
rev = lambda v: diffs[v][1] < diffs[v][0]
def nk(g, V):
    for v in V:
        if rev(v): g = add(g, v)
    return g, frozenset(tuple(-x for x in v) if rev(v) else v for v in V)
def faces(g, V):
    V = list(V)
    for tau in itertools.product(range(3), repeat=len(V)):
        gg = g
        for v, t in zip(V, tau):
            if t == 1: gg = add(gg, v)
        yield gg, frozenset(v for v, t in zip(V, tau) if t == 2)
cuts = [frozenset(c) for k in range(1, r + 1) for c in itertools.combinations(range(1, r + 1), k)]
A = set(); B = set()
for pi in itertools.permutations(range(N)):
    base = [vtx(pi[i + 1]) for i in range(r + 1)]
    for S in cuts:
        V = frozenset(sub(base[parent(S, j + 1)], base[j + 1]) for j in range(r))
        g = sub(base[max(S)], vtx(pi[0]))
        A |= {nk(*f) for f in faces(g, V)}
        B |= set(faces(*nk(g, V)))
print('N', N, 'normalizedKeys', len(A), 'normalizedConeFaceKeys', len(B), 'equal', A == B)
