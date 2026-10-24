#!/usr/bin/env python3
"""Literal emulation of the Lean dictionary normalizedKeys r (reduced simplex
coordinates, Keys/Formula/Normalize/Span + Words.parent/lastHead + Chain.vtx),
converted to full coordinates through realUnitArg (coordT y = (y_{i+1}-y_0)),
compared with scripts/vocabulary_search.dictionary(N).  Also checks the key
facts and the tree formula for kappa on every (word, face state).
Usage: python3 lean_vs_python.py N
"""
import itertools, sys, random
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary, eval_key, relu

N = int(sys.argv[1]); r = N - 2; n = r + 1          # reduced dimension n = r+1

def vtx(a):                       # Chain/Root.lean: vtx 0 = 0, vtx (i+1) = e_i
    v = [0] * n
    if a > 0: v[a - 1] = 1
    return tuple(v)
def sub(u, v): return tuple(x - y for x, y in zip(u, v))
def add(u, v): return tuple(x + y for x, y in zip(u, v))
def parent(S, j): return max([0] + [i for i in S if i < j])   # Words.lean
def lastHead(S): return max([0] + list(S))
cuts = [frozenset(c) for k in range(1, r + 1) for c in itertools.combinations(range(1, r + 1), k)]
diffs = {sub(vtx(a), vtx(b)): (a, b) for a in range(N) for b in range(N) if a != b}
assert len(diffs) == N * (N - 1)                  # simplex differences are unique
def reverseLabel(v):
    return v in diffs and diffs[v][1] < diffs[v][0]
def normalizedKey(g, V):
    for v in V:
        if reverseLabel(v): g = add(g, v)
    return g, frozenset(tuple(-x for x in v) if reverseLabel(v) else v for v in V)
def to_full(g, V):                 # realUnitArg: <g, T y>, T y = (y_{i+1} - y_0)
    h = (-sum(g),) + g
    M = []
    for v in V:
        a, b = diffs[v]           # dot v (T y) = y_a - y_b
        assert a < b, ('normalized label not increasing', v)
        M.append((a, b))
    return h, frozenset(M)

lean = set(); raw = set(); fails = {}
def fail(k): fails[k] = fails.get(k, 0) + 1
for pi in itertools.permutations(range(N)):
    apex = vtx(pi[0]); base = [vtx(pi[i + 1]) for i in range(r + 1)]
    for S in cuts:
        edges = [(parent(S, j + 1), j + 1) for j in range(r)]          # positions
        labels = [sub(base[p], base[c]) for p, c in edges]             # edgeVecs
        assert len(set(labels)) == r
        gamma = sub(base[lastHead(S)], apex)
        last = lastHead(S)
        for tau in itertools.product(range(3), repeat=r):
            g = gamma
            for v, t in zip(labels, tau):
                if t == 1: g = add(g, v)
            V = frozenset(v for v, t in zip(labels, tau) if t == 2)
            raw.add((g, V))
            h, M = to_full(*normalizedKey(g, V))
            lean.add((h, M))
            # ---- facts on this key, with the tree data of this word
            kap = [h[o] + sum(1 for i, j in M if i == o) for o in range(N)]
            ap = pi[0]
            if sum(h) != 0: fail('K1')
            if h[ap] != -1 or any(ap in e for e in M): fail('K2 apex')
            if len(M) > N - 2: fail('K4')
            if len(M) != sum(1 for t in tau if t == 2): fail('M=#hinges')
            if min(kap) < -1: fail('kappa>=-1')
            # tree formula
            for pos in range(r + 1):
                o = pi[pos + 1]
                ch = [jj for jj, (p, c) in enumerate(edges) if p == pos]
                act = sum(1 for jj in ch if tau[jj] > 0)
                plin = 1 if pos > 0 and tau[pos - 1] == 1 else 0
                f = act + (1 if pos == last else 0) - plin
                if kap[o] != f: fail('tree formula')
                childless = not ch
                spine = pos == 0 or pos in S
                if childless and kap[o] not in (0, -1):
                    fail('childless vertex kappa notin {0,-1} (spine=%s,last=%s)' % (spine, pos == last))
                if not spine and kap[o] not in (0, -1): fail('pendant kappa notin {0,-1}')
            if kap[ap] != -1: fail('kappa apex')
py, _ = dictionary(N)
print('N', N, 'raw correctionKeys', len(raw), 'lean normalizedKeys', len(lean), 'python K0', len(py),
      'equal', lean == py)
print('fact failures (counted over word-face incidences):', fails)
# function-level check: realUnitY literal vs eval_key on random points
rng = random.Random(1); bad = 0
for (g, V) in list(raw)[:3000]:
    gn, Vn = normalizedKey(g, V); key = to_full(gn, Vn)
    for _ in range(5):
        y = [rng.randint(-20, 20) for _ in range(N)]
        Ty = [y[i + 1] - y[0] for i in range(n)]
        dot = lambda u: sum(a * b for a, b in zip(u, Ty))
        lean_val = relu(dot(g) + sum(relu(dot(v)) for v in V))
        if lean_val != eval_key(key, y): bad += 1
print('raw-key realUnitY vs python normalized eval mismatches:', bad)
hs = sorted({x for h, M in lean for x in h}); print('head coefficient range', hs)
