"""MEASURED: is max_N in span(S + relu(typed dictionary))?  S = span{x_i, relu(x_i-x_j)}.
Neuron types read off the certified N=5 identity (m_ij = max(x_i,x_j)):
  star(h, w):   relu(sum_j w_j relu(x_j - x_h)),  w in {-1,0,1}^{N-1}, at least one +1 and one -1
  dmax(ij,kl):  relu(m_kl - m_ij), {i,j},{k,l} disjoint (also with shared index allowed: m_ik - m_ij)
  btype:        relu(m_kl - m_ij + (m_bi + m_bj - m_bk - m_bl)/2), b,i,j,k,l distinct
Least squares on random Gaussian points; reports relative residual and rank.
Usage: python r2_typed_dict.py N [types=star,dmax,btype] [M]"""
import sys, itertools, numpy as np
N = int(sys.argv[1]); types = (sys.argv[2] if len(sys.argv) > 2 else 'star,dmax,btype').split(',')
M = int(sys.argv[3]) if len(sys.argv) > 3 else 12000
rng = np.random.default_rng(0); X = rng.standard_normal((M, N)); r = lambda t: np.maximum(t, 0)
m = lambda i, j: np.maximum(X[:, i], X[:, j])
cols = []
if 'star' in types:
    for h in range(N):
        oth = [j for j in range(N) if j != h]
        H = np.stack([r(X[:, j] - X[:, h]) for j in oth], 1)
        for w in itertools.product((-1, 0, 1), repeat=N - 1):
            if 1 in w and -1 in w and w[next(i for i in range(N-1) if w[i])] == 1 or (1 in w and -1 in w and False):
                cols.append(r(H @ np.array(w, float)))
            elif 1 in w and -1 in w:
                cols.append(r(H @ np.array(w, float)))
if 'dmax' in types:
    P = list(itertools.combinations(range(N), 2))
    for p in P:
        for q in P:
            if p != q: cols.append(r(m(*q) - m(*p)))
if 'btype' in types:
    for b in range(N):
        oth = [j for j in range(N) if j != b]
        for i, j in itertools.combinations(oth, 2):
            for k, l in itertools.combinations([t for t in oth if t not in (i, j)], 2):
                cols.append(r(m(k, l) - m(i, j) + (m(b, i) + m(b, j) - m(b, k) - m(b, l)) / 2))
G = np.stack(cols, 1)
F = np.concatenate([X, np.stack([r(X[:, i] - X[:, j]) for i, j in itertools.combinations(range(N), 2)], 1)], 1)
B = np.concatenate([G, F], 1); y = X.max(1)
print('N', N, 'types', types, 'dictionary', G.shape[1], 'points', M)
c, res, rk, sv = np.linalg.lstsq(B, y, rcond=None)
print('rank', rk, 'of', B.shape[1], 'rel residual %.3e' % (np.linalg.norm(B @ c - y) / np.linalg.norm(y)))
