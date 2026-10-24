"""Independent check of kinks.py against scripts/vocabulary_search.cell_blocks
machinery (fine cells with 0): for every unit and braid cell pi, the kinks
reported by vocabulary_search on the fine cells refining pi, as a set of
(d, coefficient), equal the single kink (d, |lambda|) of kinks.py (or none)."""
import sys, itertools
from core import units_of
import vocabulary_search as vs
from kinks import unit_kinks
N = int(sys.argv[1])
U = units_of(N)
bad = 0
for u, key in enumerate(U):
    mine = {pi: (d, lam) for pi, d, lam in unit_kinks(N, key)}
    theirs = {}
    for order in vs.cells(N):
        rays = vs.cell_rays(N, order)
        pos = vs.cell_rank(N, order)
        kd, lin = vs.coordinates_of(N, order, rays, pos, ('key', key))
        pi = tuple(v for v in order if v != 'Z')
        for d, c in kd.items():
            theirs.setdefault(pi, set()).add((d, c))
    for pi in set(mine) | set(theirs):
        a = {mine[pi]} if pi in mine else set()
        if a != theirs.get(pi, set()):
            bad += 1
print('N', N, 'units', len(U), 'mismatches', bad)
