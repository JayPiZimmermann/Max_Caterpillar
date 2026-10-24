"""Turn a numerical fit (r2_fit.py weights) into a rational spec candidate:
normalize each neuron, snap coefficients to multiples of 1/den, refit d and R exactly
(least squares in floats, then snap), print a spec for r2_certify.py.
Usage: python r2_rationalize.py N K weights.npy [den] > spec.py"""
import sys, itertools, numpy as np
from fractions import Fraction as Fr
from r2_fit import feats
N, K, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
den = int(sys.argv[4]) if len(sys.argv) > 4 else 4
P = list(itertools.combinations(range(N), 2)); D = N - 1 + len(P)
W = np.load(fn).reshape(K, D)
rng = np.random.default_rng(0)
X = rng.standard_normal((20000, N)); F = feats(X); y = X.max(1)
B = np.concatenate([np.maximum(F @ W.T, 0), F], 1)
c, *_ = np.linalg.lstsq(B, y, rcond=None)
print('# float residual', np.linalg.norm(B @ c - y) / np.linalg.norm(y))
neur = []
for k in range(K):
    s = c[k] * np.abs(W[k]).max()
    if abs(s) < 1e-7: continue
    w = W[k] / np.abs(W[k]).max()
    # try scales so that small-denominator snapping is exact
    best = None
    for t in np.abs(w[np.abs(w) > 1e-6]):
        v = w / t; err = np.abs(v * den - np.round(v * den)).max()
        if best is None or err < best[0]: best = (err, v, s * t)
    neur.append(best)
    print('# neuron snap err %.2e' % best[0])
def tofr(v): return [Fr(int(round(x * den)), den) for x in v]
print('from fractions import Fraction as Fr\nN = %d' % N)
def lin(v):
    # features: x_i - mean (i<N-1), hinges.  convert to (l, a) on raw x
    l = [Fr(0)] * N
    for i in range(N - 1):
        l[i] += v[i]
        for j in range(N): l[j] -= v[i] / N
    a = {p: v[N - 1 + t] for t, p in enumerate(P) if v[N - 1 + t] != 0}
    return l, a
out = []
for err, v, s in neur:
    l, a = lin(tofr(v)); out.append((Fr(s).limit_denominator(64), l, a))
rl, ra = lin([Fr(x).limit_denominator(64) for x in c[K:]])
print('R = (%r, %r)' % (rl, ra))
print('NEURONS = %r' % out)
