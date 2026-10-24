"""Which single W (role matrix) families achieve top alone?  python roles_scan.py N R vals"""
import sys, itertools
import numpy as np
from collections import Counter, defaultdict
from classify import top_test
N = int(sys.argv[1]); R = int(sys.argv[2]); vals = [int(v) for v in sys.argv[3].split(',')]
pairs = [(r, s) for r in range(R) for s in range(R) if r != s]
Ws = np.array(list(itertools.product(vals, repeat=len(pairs))), dtype=np.int64)
per = defaultdict(Counter)
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
        if a.any(): per[wi][(cnt, a.tobytes())] += 1
good = []
for wi, d in per.items():
    ok, nc, nv = top_test(N, [(t, np.frombuffer(a, dtype=np.int64), m) for (t, a), m in d.items()])
    if ok: good.append(wi); print('W', dict(zip(pairs, Ws[wi].tolist())), 'types', nv, 'cross', nc, flush=True)
print('N', N, 'single-W families achieving top:', len(good))
