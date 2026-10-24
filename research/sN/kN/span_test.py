"""MEASURED: is max_N in V + span{relu(G) : G in a dictionary family}?  (least squares on
random Gaussian points; a relative residual ~1e-12 indicates membership, ~1e-2 non-membership)
Families:
  star   : G = sum_{o != c} s_o relu(x_o - x_c) (+ optional t*x_c... no), s_o in range
  star2  : stars plus 'pair-difference' neurons relu(m_ij - m_kl) and relu(m_ij - x_k)
Usage: python3 span_test.py N family W npts seed
"""
import sys, itertools
import numpy as np

N, fam, W, M, seed = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
rng = np.random.default_rng(seed)
X = rng.standard_normal((M, N))
pairs = list(itertools.combinations(range(N), 2))
H = {(i, j): np.maximum(X[:, i] - X[:, j], 0) for i in range(N) for j in range(N) if i != j}
mm = {(i, j): np.maximum(X[:, i], X[:, j]) for i, j in pairs}
base = np.concatenate([X] + [H[p][:, None] for p in pairs], 1)
cols = []
if fam.startswith('star'):
    rngv = [v for v in range(-W, W + 1)]
    for c in range(N):
        others = [o for o in range(N) if o != c]
        for s in itertools.product(rngv, repeat=N - 1):
            if sum(1 for v in s if v) < 2:
                continue
            g = sum(v * H[(o, c)] for v, o in zip(s, others) if v)
            if g.min() < -1e-12 and g.max() > 1e-12:
                cols.append(np.maximum(g, 0))
if fam == 'star2':
    for (i, j), (k, l) in itertools.permutations(pairs, 2):
        g = mm[(i, j)] - mm[(k, l)]
        cols.append(np.maximum(g, 0))
    for (i, j) in pairs:
        for k in range(N):
            if k not in (i, j):
                cols.append(np.maximum(mm[(i, j)] - X[:, k], 0))
print('dictionary size', len(cols))
A = np.concatenate([base, np.array(cols).T], 1)
y = X.max(1)
c, *_ = np.linalg.lstsq(A, y, rcond=None)
print('N %d family %s W %d: rel residual %.3e  (rank %d)' % (N, fam, W, np.linalg.norm(A @ c - y) / np.linalg.norm(y), np.linalg.matrix_rank(A, 1e-8)))
