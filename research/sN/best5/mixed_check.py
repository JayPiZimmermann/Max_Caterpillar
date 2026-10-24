"""EXACT: for a free-remainder spec (r2_certify format), count braid cells on which each neuron
changes sign (mixed) and list the cancellation partners."""
import sys, runpy, itertools
from fractions import Fraction as Fr
s = runpy.run_path(sys.argv[1]); N = s['N']
def form(l, a, perm):
    rank = {v: t for t, v in enumerate(perm)}
    v = [Fr(c) for c in l]
    for (i, j), c in a.items():
        if rank[i] < rank[j]:
            v[i] += c; v[j] -= c
    return v
cnt = [0] * len(s['NEURONS']); ex = []
for perm in itertools.permutations(range(N)):
    mixed = []
    for k, (d, l, a) in enumerate(s['NEURONS']):
        L = form(l, a, perm)
        beta = [sum(L[perm[u]] for u in range(t + 1)) for t in range(N - 1)]
        if any(b > 0 for b in beta) and any(b < 0 for b in beta):
            mixed.append(k); cnt[k] += 1
    if mixed: ex.append((perm, mixed))
print('mixed cell counts per neuron', cnt)
print('cells with mixing', len(ex), 'examples', ex[:6])
