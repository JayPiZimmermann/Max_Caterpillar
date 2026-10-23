#!/usr/bin/env python3
"""Mixed differences at the full tie with unequal steps: MD_delta f = sum_S (-1)^{m-|S|} f(delta_S),
delta_S = (delta_i [i in S]).  Can a combination kill every out-star germ s_{a,c} but not max_m?
Exact integer arithmetic, rank mod p.  Usage: outstar_md0.py m ntests seed"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import rank_mod_p
def relu(x): return x if x > 0 else 0
m, nt, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
random.seed(seed)
funcs = []
for a in range(m):
    for c in range(m):
        if a != c:
            L = [l for l in range(m) if l not in (a, c)]
            funcs.append(lambda z, a=a, c=c, L=L: relu(z[c] - z[a] + sum(relu(z[l] - z[c]) for l in L)))
subsets = list(itertools.product([0, 1], repeat=m))
def md(f, d):
    return sum((-1) ** (m - sum(S)) * f([d[i] * S[i] for i in range(m)]) for S in subsets)
rows = []; b = []
for _ in range(nt):
    d = [random.randint(1, 10 ** 4) for _ in range(m)]
    rows.append([md(f, d) for f in funcs]); b.append([md(max, d)])
A = np.array(rows, dtype=np.int64); B = np.array(b, dtype=np.int64)
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, B], axis=1))
print(f'm={m}: {len(funcs)} out-star germs, {nt} step vectors at the full tie; rank {r1}, with max {r2} -> {"SEPARATED" if r2 > r1 else "not separated"}')
