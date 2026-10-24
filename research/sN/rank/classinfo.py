import sys, itertools
from collections import Counter
from germs import localities, relabel
m = int(sys.argv[1]); N = int(sys.argv[2])
G = {g for *_, g in localities(N, m)}
Gc = {relabel(g, p) for g in G for p in itertools.permutations(range(m))}
print('raw', len(G), 'closed', len(Gc))
print('v range', min(min(g[0]) for g in Gc), max(max(g[0]) for g in Gc))
print('|M| hist', Counter(len(g[1]) for g in Gc))
# in unnormalized "tree" form: kappa-like? print raw germs
for g in sorted(G, key=str): print(g[0], sorted(g[1]))
