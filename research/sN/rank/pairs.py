"""t*_m >= s+1 certificate by stencils: for every set S of s full germs there is a
mixed m-th difference D (from the family) with D max != 0 and D g = 0 for g in S.
usage: pairs.py m N B cvals s"""
import sys, itertools
import numpy as np
from germs import localities, relabel
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
m, N, B = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
CV = [int(x) for x in sys.argv[4].split(',')]; s = int(sys.argv[5])
def isfull(g):
    h, M = g
    return all(h[t] != 0 or any(t in e for e in M) for t in range(len(h)))
G = {g for *_, g in localities(N, m)}
Gc = {relabel(g, p) for g in G for p in itertools.permutations(range(m))}
full = sorted([g for g in Gc if isfull(g)], key=str)
rows = {}
for a in [(0,) + t for t in itertools.product(range(-B, B + 1), repeat=m - 1)]:
    for c in itertools.product(CV, repeat=m):
        pts = []
        for S in range(1 << m):
            p = list(a)
            for i in range(m):
                if S >> i & 1: p[i] += c[i]
            pts.append(((-1) ** (m - bin(S).count('1')), tuple(p)))
        dm = sum(sg * max(p) for sg, p in pts)
        if dm == 0: continue
        row = tuple(sum(sg * vs.eval_key(g, p) for sg, p in pts) != 0 for g in full)
        rows.setdefault(row, (a, c, dm))
Z = np.array([[not x for x in r] for r in rows], dtype=bool)   # Z[i,g]: functional i kills g
keys = list(rows.values())
n = len(full)
print(f'm={m} full germs {n}, distinct functionals {len(Z)}')
bad = []
for S in itertools.combinations(range(n), s):
    if not Z[:, list(S)].all(1).any():
        bad.append(S)
print(f'sets of size {s} not killed by any functional: {len(bad)}')
for S in bad[:10]:
    print('  ', [full[i] for i in S])
