"""EXACT: 3-locality passing sets of the neurons of a spec (r2_certify format).
Neuron <l,x> + sum c_ij relu(x_i-x_j) (i<j) is converted to (a, kappa):
relu(x_i-x_j) = (x_i-x_j)/2 + |x_i-x_j|/2, so a_ij = c_ij/2, l' = l + sum c_ij (e_i-e_j)/2,
kappa_v = (l'_v + A_v)/2."""
import sys, runpy
from fractions import Fraction as Fr
from passing import localities, passes
s = runpy.run_path(sys.argv[1]); N = s['N']
locs = list(localities(N))
cover = set()
for k, (d, l, c) in enumerate(s['NEURONS']):
    a = {p: Fr(v) / 2 for p, v in c.items() if v}
    lp = [Fr(x) for x in l]
    for (i, j), v in c.items():
        lp[i] += Fr(v) / 2; lp[j] -= Fr(v) / 2
    A = [sum(v for p, v in a.items() if t in p) for t in range(N)]
    kappa = [(lp[t] + A[t]) / 2 for t in range(N)]
    assert sum(lp) == 0
    P = [L for L in locs if passes(a, kappa, *L)]
    cover |= set(P)
    print('neuron', k, 'd', d, 'passes', len(P), sorted(P))
print('covered', len(cover), 'of', len(locs))
