"""Vectorised double-star tree units with heads (see fam_dstar_head.py). python dstar_fast.py n R"""
import sys, itertools
import numpy as np
from fastsym import top_test_fast
n = int(sys.argv[1]); R = int(sys.argv[2])
roles = [(lf, h) for lf in (0, 1, 2) for h in range(-R, R + 1)]
nr = len(roles); m = n - 2
grid = np.array(list(itertools.product(range(nr), repeat=m)), dtype=np.int64)   # assignments
cnt = np.zeros((len(grid), nr), dtype=np.int64)
for j in range(m): np.add.at(cnt, (np.arange(len(grid)), grid[:, j]), 1)
base = (nr + 1)
cid = (cnt * (base ** np.arange(nr))).sum(1)          # multiset code
Ts = []; As = []
for p1 in range(n):
    for p2 in range(n):
        if p1 == p2: continue
        others = [o for o in range(n) if o not in (p1, p2)]
        for ce in (0, 1):
            for h2 in range(-R, R + 1):
                A = np.zeros((len(grid), n), dtype=np.int16)
                A[:, p2] += h2; hs = np.full(len(grid), h2, dtype=np.int16)
                if ce and p2 < p1: A[:, p2] += 1; A[:, p1] -= 1
                for j, o in enumerate(others):
                    lf = np.array([r[0] for r in roles])[grid[:, j]]
                    h = np.array([r[1] for r in roles])[grid[:, j]]
                    A[:, o] += h; hs += h
                    for c, val in ((p1, 1), (p2, 2)):
                        if o < c:
                            msk = lf == val; A[msk, o] += 1; A[msk, c] -= 1
                A[:, p1] -= hs
                keep = A.any(1)
                Ts.append(((ce * (2 * R + 1) + (h2 + R)) * (base ** nr) + cid)[keep]); As.append(A[keep])
T = np.concatenate(Ts); A = np.concatenate(As)
u, T = np.unique(T, return_inverse=True)
if len(sys.argv) > 3:
    from fastsym import top_lp
    st, w, sh = top_lp(n, T.ravel(), A)
    print("n", n, "R", R, "LP status", st, "shape", sh, "support", None if w is None else int((abs(w) > 1e-9).sum()), flush=True); sys.exit()
ok, nc, nt = top_test_fast(n, T.ravel(), A)
print('n', n, 'R', R, 'neurons', len(A), 'types', nt, 'cross', nc, 'TOP', ok, flush=True)
