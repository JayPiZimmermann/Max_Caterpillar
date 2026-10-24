"""Double out-star tree units with integer heads: centres c1 (parent) -> c2 (child) optional hinge,
 others are leaves of c1, of c2, or isolated; head h integer sum 0, |h_o|<=R for non-centres,
 h_c2 in [-R,R], h_c1 = -sum.   python fam_dstar_head.py n R"""
import sys, itertools
import numpy as np
from classify import top_test
n = int(sys.argv[1]); R = int(sys.argv[2])
roles = [(lf, h) for lf in (0, 1, 2) for h in range(-R, R + 1)]
neur = []
for p1 in range(n):
    for p2 in range(n):
        if p1 == p2: continue
        others = [o for o in range(n) if o not in (p1, p2)]
        for ce in (0, 1):
            for h2 in range(-R, R + 1):
                for asg in itertools.product(range(len(roles)), repeat=n - 2):
                    a = np.zeros(n, dtype=np.int64); hs = h2; a[p2] += h2
                    if ce and p2 < p1: a[p2] += 1; a[p1] -= 1          # sigma(x_c2 - x_c1)
                    for o, ri in zip(others, asg):
                        lf, h = roles[ri]; a[o] += h; hs += h
                        c = p1 if lf == 1 else (p2 if lf == 2 else None)
                        if c is not None and o < c: a[o] += 1; a[c] -= 1
                    a[p1] -= hs
                    if not a.any(): continue
                    neur.append(((ce, h2, tuple(sorted(asg))), a, 1))
ok, nc, nv = top_test(n, neur)
print('n', n, 'R', R, 'types', nv, 'cross', nc, 'TOP', ok, flush=True)
