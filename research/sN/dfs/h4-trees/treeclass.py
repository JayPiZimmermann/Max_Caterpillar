#!/usr/bin/env python3
"""General tree vocabulary (branch h4-trees).

Class G: apex a, spanning tree tau on the other N-1 labels, head vertex r,
generators g_e = eps_e (e_i - e_j) with arbitrary orientation eps_e; the
pyramid conv(0, e_r - e_a + sum_e [0, g_e]) and all its faces through 0:
each edge omitted / linear (+-) / hinge (+-).  Keys are normalized as in the
paper: (h, M), M a set of (i,j) with i<j standing for relu(x_i - x_j).

Sub-classes:
  'G'    all trees, all orientations, all head vertices
  'star' stars only (all orientations, all head vertices)
  'out'  every edge oriented away from the head vertex r (g = e_child - e_parent)
  'in'   every edge oriented towards r (g = e_parent - e_child)
"""
import itertools

def norm(N, lin, hinges):
    h = [0] * N; M = set()
    for i, j in lin:
        h[i] += 1; h[j] -= 1
    for i, j in hinges:
        if i > j:
            h[i] += 1; h[j] -= 1; i, j = j, i
        M.add((i, j))
    return (tuple(h), frozenset(M))

def pruefer_trees(vs):
    n = len(vs)
    if n == 1:
        yield []; return
    if n == 2:
        yield [(vs[0], vs[1])]; return
    for code in itertools.product(range(n), repeat=n - 2):
        deg = [1] * n
        for c in code: deg[c] += 1
        edges = []
        for c in code:
            leaf = min(i for i in range(n) if deg[i] == 1)
            edges.append((vs[leaf], vs[c])); deg[leaf] -= 1; deg[c] -= 1
        u, w = [i for i in range(n) if deg[i] == 1]
        edges.append((vs[u], vs[w]))
        yield edges

def is_star(edges):
    from collections import Counter
    cnt = Counter(v for e in edges for v in e)
    return len(edges) <= 1 or max(cnt.values()) == len(edges)

def orient_from(edges, r):
    """(parent, child) pairs of the tree rooted at r."""
    adj = {}
    for u, w in edges:
        adj.setdefault(u, []).append(w); adj.setdefault(w, []).append(u)
    out = []; seen = {r}; st = [r]
    while st:
        u = st.pop()
        for w in adj.get(u, []):
            if w not in seen:
                seen.add(w); out.append((u, w)); st.append(w)
    return out

def faces(N, a, edges, r, mode):
    """Yield normalized keys of all faces.  mode in G/star/out/in."""
    if mode in ('out', 'in'):
        pc = orient_from(edges, r)
        gens = [[(c, p)] if mode == 'out' else [(p, c)] for p, c in pc]
    else:
        gens = [[(u, w), (w, u)] for u, w in edges]
    opts = []
    for g in gens:
        o = [None]
        for d in g:
            o.append(('lin', d)); o.append(('hin', d))
        opts.append(o)
    for ch in itertools.product(*opts):
        lin = [(r, a)] + [d for c in ch if c and c[0] == 'lin' for d in [c[1]]]
        hin = [c[1] for c in ch if c and c[0] == 'hin']
        yield norm(N, lin, hin)

def full_keys(N, a, edges, r, mode):
    """Only the all-hinge top units (one per orientation pattern)."""
    if mode in ('out', 'in'):
        pc = orient_from(edges, r)
        yield norm(N, [(r, a)], [(c, p) if mode == 'out' else (p, c) for p, c in pc])
    else:
        for eps in itertools.product([0, 1], repeat=len(edges)):
            yield norm(N, [(r, a)], [(u, w) if s == 0 else (w, u) for (u, w), s in zip(edges, eps)])

def vocabulary(N, mode, top_only=False):
    K = set()
    for a in range(N):
        vs = [v for v in range(N) if v != a]
        for edges in pruefer_trees(vs):
            if mode == 'star' and not is_star(edges): continue
            for r in vs:
                gen = full_keys if top_only else faces
                for k in gen(N, a, edges, r, 'G' if mode == 'star' else mode):
                    K.add(k)
    return K

def is_aux(key):
    h, M = key
    return not M and sorted(h) == [-1] + [0] * (len(h) - 2) + [1]

def is_affine(key):
    return not key[1]
