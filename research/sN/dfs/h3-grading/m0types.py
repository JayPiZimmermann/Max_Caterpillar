import sys, collections
from common import keys
for N in map(int, sys.argv[1:]):
    hs = {k[0] for k in keys(N) if not k[1]}
    lines = {min(h, tuple(-t for t in h)) for h in hs}
    c = collections.Counter(tuple(sorted(h, reverse=True)) for h in hs)
    print(N, 'keys', len(hs), 'lines', len(lines), sorted(c.items(), key=lambda t: -t[1]))
