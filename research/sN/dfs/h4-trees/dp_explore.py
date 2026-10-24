#!/usr/bin/env python3
"""Collect child summaries (sigma, gamma, omega, alpha) of rooted subtrees (h4-trees)."""
import itertools, random, sys
from fractions import Fraction
from dpV2 import node
from classW_fast import free_trees
random.seed(1)
pts = set()
def summ(st): return (st['s'], st['gamma'], st['omega'], st['alpha'])
# all rooted trees up to n vertices hanging below a parent (planted)
for n in range(1, 8):
    for edges in (free_trees(list(range(n))) if n > 1 else [[]]):
        adj = {v: [] for v in range(n)}
        for u, w in edges: adj[u].append(w); adj[w].append(u)
        for r in range(n):
            def rec(v, p, e):
                return node(e[v], [rec(w, v, e) for w in adj[v] if w != p])
            for e in itertools.product(range(3), repeat=n):
                pts.add(summ(rec(r, None, e)))
P = [tuple(float(t) for t in p) for p in pts]
print(len(P), 'summaries')
import numpy as np
A = np.array(P)
print('max sigma, gamma, omega, alpha:', A.max(axis=0))
print('max sigma+omega', (A[:,0]+A[:,2]).max(), ' max alpha+gamma', (A[:,3]+A[:,1]).max())
for lam in [0.5, 1, 2]:
    print('max alpha + lam*gamma', lam, (A[:,3] + lam*A[:,1]).max(), ' max sigma+omega+lam*gamma', (A[:,0]+A[:,2]+lam*A[:,1]).max())
np.save('logs/summaries.npy', A)
