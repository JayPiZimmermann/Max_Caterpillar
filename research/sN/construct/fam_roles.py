"""Role-blow-up families (no specials): vertices get roles 0..R-1; g = sum over ordered role
pairs (r,s) W[r][s] * sum_{i in r, j in s, i!=j} sigma(x_i - x_j).  W entries in vals.
Usage: python fam_roles.py N R vals(comma)"""
import sys, itertools
import numpy as np
from collections import Counter
from classify import top_test
N = int(sys.argv[1]); R = int(sys.argv[2]); vals = [int(v) for v in sys.argv[3].split(',')]
pairs = [(r, s) for r in range(R) for s in range(R)]
neur = Counter()
assigns = list(itertools.product(range(R), repeat=N))
# basis: for each assignment, for each ordered role pair, a-vector
for asg in assigns:
    cnt = tuple(asg.count(r) for r in range(R))
    B = {}
    for (r, s) in pairs:
        a = np.zeros(N, dtype=np.int64)
        for i in range(N):
            for j in range(i + 1, N):   # i above j: sigma(x_i-x_j)=x_i-x_j active
                if asg[i] == r and asg[j] == s: a[i] += 1; a[j] -= 1
        B[(r, s)] = a
    for W in itertools.product(vals, repeat=len(pairs)):
        a = sum(w * B[p] for w, p in zip(W, pairs) if w)
        if isinstance(a, int): continue
        neur[((W, cnt), tuple(a))] += 1
ok, nc, nv = top_test(N, [(t, np.array(a), m) for (t, a), m in neur.items()])
print('N', N, 'R', R, 'vals', vals, 'types', nv, 'cross', nc, 'TOP', ok)
