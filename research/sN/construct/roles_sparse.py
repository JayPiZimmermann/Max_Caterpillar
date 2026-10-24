import sys, itertools
import numpy as np
from collections import Counter
from math import factorial
from l1sparse import sparse_top
N = int(sys.argv[1]); R = int(sys.argv[2]); vals = [int(v) for v in sys.argv[3].split(',')]
pairs = [(r, s) for r in range(R) for s in range(R) if r != s]
Ws = np.array(list(itertools.product(vals, repeat=len(pairs))), dtype=np.int64)
neur = Counter()
for asg in itertools.product(range(R), repeat=N):
    cnt = tuple(asg.count(r) for r in range(R))
    B = np.zeros((len(pairs), N), dtype=np.int64)
    for k, (r, s) in enumerate(pairs):
        for i in range(N):
            for j in range(i + 1, N):
                if asg[i] == r and asg[j] == s: B[k, i] += 1; B[k, j] -= 1
    A = Ws @ B
    for wi in range(len(Ws)):
        a = A[wi]
        if a.any(): neur[((wi, cnt), a.tobytes())] += 1
neurons = [(t, np.frombuffer(a, dtype=np.int64), m) for (t, a), m in neur.items()]
def orbit(t):
    wi, cnt = t; o = factorial(N)
    for c in cnt: o //= factorial(c)
    return o
types = {t for t, _, _ in neurons}
r = sparse_top(N, neurons, cost={t: orbit(t) for t in types})
ok, sol, fl = r
print('exact ok', ok, 'support', len(sol), 'total orbit', sum(orbit(t) for t in sol))
for t, v in sol.items():
    print(dict(zip(pairs, Ws[t[0]].tolist())), 'counts', t[1], 'w', v, 'orbit', orbit(t))
