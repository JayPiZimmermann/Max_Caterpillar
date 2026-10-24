"""Exploration: is max_t in the span of the hinge-path unit's T-germ classes?

For every top-set size t, collects all S_t-images of the T-germs of the hinge
path units u* (head e_last - e_apex, hinge path avoiding the apex, N-3 hinges)
over all T where (a) holds for some lower composition, and reports the exact
rank with and without max_t.  If max_t is NOT in the span, some functional on
t-germs kills every relabelled u* at that stratum type but detects max.
Usage: python3 explore_ustar.py N tmax
"""
import itertools
import pickle
import sys

from germs import class_coords
from lp import perm_germ, rank_of

N = int(sys.argv[1])
tmax = int(sys.argv[2])
_, data = pickle.load(open(f'data/strata_{N}.pkl', 'rb'))
ustar = [(k, res) for k, res in data if k[0] == tuple([-1] + [0] * (N - 2) + [1])
         and len(k[1]) == N - 3 and all(i != 0 for e in k[1] for i in e)]
for k, res in ustar:
    print(N, 'unit', k[0], sorted(k[1]), flush=True)
    for t in range(3, tmax + 1):
        gs = set()
        byc = {}
        for T, (g, cn) in res.items():
            if len(T) == t:
                for p in itertools.permutations(range(t)):
                    gs.add(perm_germ(g, p))
                for c, n in cn.items():
                    byc[c] = byc.get(c, 0) + n
        if not gs:
            continue
        gs = sorted(gs, key=str)
        rk, co, mx = class_coords(t, gs)
        r1 = rank_of([list(c) for c in co])
        r2 = rank_of([list(c) for c in co] + [list(mx)])
        print(' t', t, 'germs', len(gs), 'rank', r1, 'with max', r2,
              'max in span' if r1 == r2 else 'MAX NOT IN SPAN', 'counts', byc, flush=True)
