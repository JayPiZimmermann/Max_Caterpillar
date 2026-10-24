"""S_n-symmetric version of fam_cps (all centres share the identity chamber)."""
import sys, itertools
import numpy as np
from classify import top_test
n = int(sys.argv[1]); MUS = [int(v) for v in sys.argv[2].split(',')]
SV = [int(v) for v in sys.argv[3].split(',')] if len(sys.argv) > 3 else [-1, 0, 1]
neur = []
for p in range(n):
    others = [o for o in range(n) if o != p]       # positions; centre at position p
    pairs = list(itertools.combinations(others, 2))
    shapes = [(0, None, None)] + [(mu, P, Q) for mu in MUS for P in pairs for Q in pairs if P != Q]
    for mu, P, Q in shapes:
        for svals in itertools.product(SV, repeat=n - 1):
            s = dict(zip(others, svals))
            a = np.zeros(n, dtype=np.int64)
            if mu:
                a[min(P)] += mu; a[min(Q)] -= mu
            for o in others:
                if s[o] and o < p: a[o] += s[o]; a[p] -= s[o]
            if not a.any(): continue
            if mu == 0: t = ('star', tuple(sorted(s.values())))
            else:
                sh = set(P) & set(Q)
                t = (mu, tuple(sorted(s[v] for v in P if v not in sh)), tuple(sorted(s[v] for v in Q if v not in sh)),
                     tuple(s[v] for v in sh), tuple(sorted(s[v] for v in others if v not in P and v not in Q)))
            neur.append((t, a, 1))
ok, nc, nv = top_test(n, neur)
print('n', n, 'mus', MUS, 'SV', SV, 'types', nv, 'cross', nc, 'TOP', ok, flush=True)
