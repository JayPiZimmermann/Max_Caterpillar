import sys, itertools
import numpy as np
from nonsym import solve_sparse, solve_sparse_exact
n = int(sys.argv[1]); k = int(sys.argv[2]); mode = sys.argv[3]
E = list(itertools.combinations(range(n), 2))
def forest(es):
    par = list(range(n))
    def f(a):
        while par[a] != a: a = par[a]
        return a
    for a, b in es:
        ra, rb = f(a), f(b)
        if ra == rb: return False
        par[ra] = rb
    return True
F = [es for es in itertools.combinations(E, k) if forest(es)]
LW = []; seen = set()
for A in F:
    for B in F:
        if set(A) & set(B) or (B, A) in seen: continue
        seen.add((A, B))
        l = [0] * n; W = {}
        for (i, j) in A: l[j] += 1; W[(i, j)] = W.get((i, j), 0) + 1
        for (i, j) in B: l[j] -= 1; W[(i, j)] = W.get((i, j), 0) - 1
        LW.append((l, W))
print('atoms', len(LW), flush=True)
if mode == 'top':
    best, rows, T = solve_sparse(n, LW); supp, x = best
else:
    supp, x = solve_sparse_exact(n, LW)
print('best', len(supp))
