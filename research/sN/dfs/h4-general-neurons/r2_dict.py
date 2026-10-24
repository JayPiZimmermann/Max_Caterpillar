"""MEASURED: is max_N in span(S + relu(dictionary))?  Dictionary = images of the N=5 neurons
(r2_spec_N5_k4.py) under all injections [5] -> [N].  Least squares on random points."""
import sys, itertools, runpy, numpy as np
N = int(sys.argv[1])
s = runpy.run_path('r2_spec_N5_k4.py')
P = list(itertools.combinations(range(N), 2))
def vec(l, a, phi):
    v = np.zeros(N + len(P))
    for i in range(5): v[phi[i]] += float(l[i])
    for (i, j), c in a.items():
        u, w = phi[i], phi[j]
        if u < w: v[N + P.index((u, w))] += float(c)
        else:  # relu(x_w - x_u) with w<u : relu(x_u-x_w) = (x_u-x_w) + relu(x_w-x_u)
            v[u] += float(c); v[w] -= float(c); v[N + P.index((w, u))] += float(c)
    return v
D = {}
for phi in itertools.permutations(range(N), 5):
    for d, l, a in s['NEURONS']:
        v = vec(l, a, phi); D[tuple(np.round(v, 6))] = v
G = np.array(list(D.values())); print('dictionary size', len(G))
rng = np.random.default_rng(0); X = rng.standard_normal((6000, N))
F = np.concatenate([X, np.stack([np.maximum(X[:, i] - X[:, j], 0) for i, j in P], 1)], 1)
B = np.concatenate([np.maximum(F @ G.T, 0), F], 1); y = X.max(1)
c, *_ = np.linalg.lstsq(B, y, rcond=None)
print('N', N, 'rel residual', np.linalg.norm(B @ c - y) / np.linalg.norm(y))
