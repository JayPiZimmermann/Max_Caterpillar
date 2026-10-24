"""EXACT: for each neuron of a spec, the braid cells on which its linear form changes sign
(crosses zero strictly inside the cell), decided by the ray values of the simplicial cell
(cell = cone over rays e_{pi(0..t)}, plus the lineality +-1)."""
import sys, runpy, itertools
from fractions import Fraction as Fr
from r2_certify import lin_on_cell
s = runpy.run_path(sys.argv[1]); N = s['N']
for k, (d, l, a) in enumerate(s['NEURONS']):
    cross = []
    for perm in itertools.permutations(range(N)):
        rank = {perm[t]: t for t in range(N)}
        v = lin_on_cell(N, l, a, rank)
        if sum(v) != 0: print('not translation invariant'); 
        rv = [sum(v[perm[i]] for i in range(t + 1)) for t in range(N - 1)]
        if any(x > 0 for x in rv) and any(x < 0 for x in rv):
            cross.append((perm, [str(x) for x in rv]))
    print('neuron', k, 'd', d, 'crosses in', len(cross), 'cells')
    for c in cross[:40]: print('   ', c)
