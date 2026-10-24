import sys, time, numpy as np
from modp import Space
from cuts import hyperplane_cut
N = int(sys.argv[1]); trials = int(sys.argv[2])
sp = Space(N)
rng = np.random.default_rng(0)
sizes = []
t0 = time.time()
for tr in range(trials):
    order = list(rng.permutation(sp.n))
    y, cut = hyperplane_cut(sp.G, sp.t, order)
    sizes.append(len(cut))
print('n', sp.n, 'q', sp.q, 'random-order cut sizes', sorted(sizes), time.time() - t0)
