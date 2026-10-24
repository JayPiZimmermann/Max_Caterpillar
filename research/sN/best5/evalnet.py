"""Float spot check of a network JSON against max (independent of cert.py)."""
import sys, json, numpy as np
from fractions import Fraction as Fr
n = json.load(open(sys.argv[1]))
f = lambda M: np.array([[float(Fr(c)) for c in r] for r in M])
A, W, d = f(n['first_layer']), f(n['second_layer']), np.array([float(Fr(c)) for c in n['output']])
X = np.random.default_rng(1).standard_normal((20000, n['N']))
F = np.maximum(np.maximum(X @ A.T, 0) @ W.T, 0) @ d
print('h1 %d h2 %d max abs err on 2e4 Gaussian points: %.2e' % (len(A), len(W), np.abs(F - X.max(1)).max()))
