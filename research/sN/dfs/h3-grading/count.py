import sys, collections
from common import keys, polydim
for N in map(int, sys.argv[1:]):
    ks = keys(N)
    c = collections.Counter((polydim(k), len(k[1])) for k in ks)
    print(N, len(ks), sorted(c.items()), flush=True)
