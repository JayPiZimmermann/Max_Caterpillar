"""Out-star tree units with large integer heads (coordinator hint):
 U = sigma(<h,x> + sum_{o in L} sigma(x_o - x_c)),  h integer, sum h = 0, |h_o| <= R (o != c),
 leaf weights in LW (default {0,1}).  S_n-symmetric top test (classify.top_test).
python fam_bighead.py n R [leafvals]"""
import sys, itertools
import numpy as np
from classify import top_test
n = int(sys.argv[1]); R = int(sys.argv[2])
LV = [int(v) for v in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0, 1]
roles = [(lf, h) for lf in LV for h in range(-R, R + 1)]
neur = []
for p in range(n):                      # centre position in identity chamber (0 = top)
    others = [o for o in range(n) if o != p]
    for asg in itertools.product(range(len(roles)), repeat=n - 1):
        a = np.zeros(n, dtype=np.int64); hc = 0
        for o, ri in zip(others, asg):
            lf, h = roles[ri]
            a[o] += h; hc -= h
            if lf and o < p: a[o] += lf; a[p] -= lf
        a[p] += hc
        if not a.any(): continue
        neur.append((tuple(sorted(asg)), a, 1))
ok, nc, nv = top_test(n, neur)
print('n', n, 'R', R, 'LV', LV, 'types', nv, 'cross', nc, 'TOP', ok, flush=True)
