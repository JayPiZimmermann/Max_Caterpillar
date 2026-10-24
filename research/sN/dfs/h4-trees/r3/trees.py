#!/usr/bin/env python3
"""Free (unlabelled) trees on n vertices, one labelled representative each (h4-trees r3).
Grown by leaf addition from n-1 with AHU canonical dedup.  Usage: trees.py n > trees_n.txt
Output line: n u1 w1 u2 w2 ... (edges)."""
import sys
def canon(n, edges):
    adj = [[] for _ in range(n)]
    for u, w in edges: adj[u].append(w); adj[w].append(u)
    def enc(v, p): return '(' + ''.join(sorted(enc(w, v) for w in adj[v] if w != p)) + ')'
    return min(enc(v, -1) for v in range(n))
def trees(n):
    if n == 1: return [[]]
    out = {}
    for E in trees(n - 1):
        for v in range(n - 1):
            F = E + [(v, n - 1)]; c = canon(n, F)
            if c not in out: out[c] = F
    return list(out.values())
n = int(sys.argv[1])
for E in trees(n):
    print(n, ' '.join(f'{u} {w}' for u, w in E))
