"""For every flat (from flats_fast dump), sample exact random elements (several seeds) and
record the max number of localities with nonzero mixed difference of sigma(germ). Measured
lower bound on mu(N,m) = max_g #passed localities."""
import json, sys
from inspect_flat import analyse
from braidlib import localities
N, m = int(sys.argv[1]), int(sys.argv[2]); seeds = int(sys.argv[3]) if len(sys.argv) > 3 else 6
tops = json.load(open(f"flats_{N}_{m}_top.json"))
total = len(list(localities(N, m)))
best = (0, None, None)
for S in tops:
    S = [(tuple(T), tuple(r)) for T, r in S]
    for s in range(seeds):
        th, van, good = analyse(N, m, S, seed=s, show=False)
        if len(good) > best[0]:
            best = (len(good), S, s)
print("N", N, "m", m, "localities", total, "max good passes (measured)", best[0])
analyse(N, m, best[1], seed=best[2], show=True)
