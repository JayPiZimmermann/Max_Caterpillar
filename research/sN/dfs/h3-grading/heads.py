"""Check: heads of |M|=0 keys = {h in Z^N : sum h = 0, h >= -1, 2 <= #{h_i=-1} <= N-2}, and
#lines = sum_{k>=2} C(N,k) C(N-1,k) [k<=N-2] - sum_k C(N,k) C(N-k,k)/2.  Exact enumeration against the dictionary."""
import sys, itertools
from math import comb
from common import keys
for N in map(int, sys.argv[1:]):
    hs = {k[0] for k in keys(N) if not k[1]}
    pred = set()
    for h in itertools.product(range(-1, N), repeat=N):
        if sum(h) == 0 and 2 <= sum(1 for t in h if t == -1) <= N - 2: pred.add(h)
    lines = len({min(h, tuple(-t for t in h)) for h in hs})
    fl = sum(comb(N, k) * comb(N - 1, k) for k in range(2, N - 1)) - sum(comb(N, k) * comb(N - k, k) for k in range(2, N)) // 2
    print(N, 'heads', len(hs), 'pred', len(pred), 'equal', hs == pred, 'lines', lines, 'formula', fl)
