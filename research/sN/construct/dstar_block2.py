import sys, itertools
import numpy as np
from blocksym import TopSystem
n = int(sys.argv[1]); R = int(sys.argv[2]); RC = int(sys.argv[3])
roles = [(lf, h) for lf in (0, 1, 2) for h in range(-R, R + 1)]
nr = len(roles); m = n - 2
grid = np.array(list(itertools.product(range(nr), repeat=m)), dtype=np.int8)
cnt = np.zeros((len(grid), nr), dtype=np.int64)
for j in range(m): np.add.at(cnt, (np.arange(len(grid)), grid[:, j].astype(np.int64)), 1)
cid = (cnt * ((m + 1) ** np.arange(nr))).sum(1)
ucid, cidx = np.unique(cid, return_inverse=True); cidx = cidx.ravel(); nc = len(ucid)
LF = np.array([r[0] for r in roles]); HH = np.array([r[1] for r in roles])
S = TopSystem(n)
for p1 in range(n):
    for p2 in range(n):
        if p1 == p2: continue
        others = [o for o in range(n) if o not in (p1, p2)]
        for ce in (0, 1):
            for h2 in range(-RC, RC + 1):
                A = np.zeros((len(grid), n), dtype=np.int16)
                A[:, p2] += h2; hs = np.full(len(grid), h2, dtype=np.int16)
                if ce and p2 < p1: A[:, p2] += 1; A[:, p1] -= 1
                for j, o in enumerate(others):
                    lf = LF[grid[:, j]]; h = HH[grid[:, j]]
                    A[:, o] += h; hs += h
                    for c, val in ((p1, 1), (p2, 2)):
                        if o < c:
                            msk = lf == val; A[msk, o] += 1; A[msk, c] -= 1
                A[:, p1] -= hs
                keep = A.any(1)
                T = (ce * (2 * RC + 1) + (h2 + RC)) * nc + cidx
                S.add(T[keep], A[keep])
ntypes = 2 * (2 * RC + 1) * nc
st, w, sh = S.solve_lp(ntypes)
print('n', n, 'R', R, 'RC', RC, 'LP status', st, 'shape', sh, 'support', None if w is None else int((abs(w) > 1e-9).sum()), flush=True)
