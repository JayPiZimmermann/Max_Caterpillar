import sys, itertools, runpy
import numpy as np
from math import comb, factorial
from l1sparse import sparse_top
n = int(sys.argv[1]); MUS = [int(v) for v in sys.argv[2].split(',')]
sys.argv = ['fam_cps2.py', str(n), sys.argv[2]]
src = open('fam_cps2.py').read().split('ok, nc, nv = top_test')[0]
g = {}; exec(src, g); neur = g['neur']
from collections import Counter
cnt = Counter(t for t, a, m in neur)   # neurons of the type in the identity chamber
# orbit size = (#neurons of type in one chamber) * n! / n!  -> each orbit member appears in exactly one chamber position pattern...
# total orbit size = cnt[t] * n! / (number of chambers each neuron is seen in = 1 representative per chamber)?  use cnt as proxy weight
r = sparse_top(n, [(t, a, m) for t, a, m in neur], cost={t: cnt[t] for t in cnt})
ok, sol, fl = r
print('exact', ok, 'support', len(sol))
for t, v in sorted(sol.items(), key=lambda kv: str(kv[0])): print(t, v, 'cnt', cnt[t])
