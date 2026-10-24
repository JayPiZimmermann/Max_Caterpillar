"""EXACT: the linear space W_all of neuron weights (a_ij, kappa_v) satisfying the
3-locality value equations E_L for ALL 3-localities of N (plus sum kappa = sum a),
and the germs of such neurons at each T.  Used to decide whether ONE general neuron
can pass every 3-locality (k = 1 lower bound)."""
import sys, itertools
from fractions import Fraction as Fr
from passing import localities, germ, germ_passes
from flats2 import nullspace_q
N = int(sys.argv[1])
pr = list(itertools.combinations(range(N), 2)); idx = {p: i for i, p in enumerate(pr)}
nv = len(pr) + N
rows = [[-1] * len(pr) + [1] * N]
for T, order in localities(N):
    above = list(T)
    for o in order:
        r = [0] * nv
        for j in above:
            r[idx[(min(o, j), max(o, j))]] += 1
        r[len(pr) + o] -= 1
        rows.append(r); above.append(o)
B = nullspace_q(rows, nv)
print('dim W_all =', len(B))
for b in B:
    print(' a:', {p: str(b[i]) for i, p in enumerate(pr) if b[i]}, 'kappa:', [str(x) for x in b[len(pr):]])
