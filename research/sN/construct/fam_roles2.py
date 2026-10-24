"""Role families, off-diagonal W only, vectorised.  python fam_roles2.py N R vals [diag]"""
import sys, itertools
import numpy as np
from collections import Counter
from classify import top_test
N = int(sys.argv[1]); R = int(sys.argv[2]); vals = [int(v) for v in sys.argv[3].split(',')]
diag = len(sys.argv) > 4
pairs = [(r, s) for r in range(R) for s in range(R) if r != s or diag]
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
        if not a.any(): continue
        neur[((wi, cnt), a.tobytes())] += 1
ok, nc, nv = top_test(N, [(t, np.frombuffer(a, dtype=np.int64), m) for (t, a), m in neur.items()])
print('N', N, 'R', R, 'vals', vals, 'diag', diag, 'types', nv, 'cross', nc, 'TOP', ok, flush=True)
