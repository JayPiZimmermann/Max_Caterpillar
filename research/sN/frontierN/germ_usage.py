"""For an exact network (json: first_layer, second_layer, output), list for every S (|S|>=3)
the neurons vanishing at 1_S (Z(S)) and the rank of their odd germ functionals restricted to
z_S-directions (z supported on S, mod 1_S), versus the Lemma-3 requirement ceil(|S|/2)-1."""
import sys, json, itertools
from fractions import Fraction as Fr
import sympy as sp
d = json.load(open(sys.argv[1])); N = d['N']
A = [[Fr(v) for v in r] for r in d['first_layer']]
W = [[Fr(v) for v in r] for r in d['second_layer']]
h1, h2 = len(A), len(W)
use = [0]*h2
for k in range(3, N+1):
    for S in itertools.combinations(range(N), k):
        p = [1 if i in S else 0 for i in range(N)]
        ap = [sum(a[i]*p[i] for i in range(N)) for a in A]
        g = [sum(W[kk][j]*max(ap[j], 0) for j in range(h1)) for kk in range(h2)]
        Z = [kk for kk in range(h2) if g[kk] == 0]
        rows = []
        for kk in Z:
            o = [sum(W[kk][j]*(1 + (1 if ap[j] > 0 else (-1 if ap[j] < 0 else 0)))*A[j][i]
                     for j in range(h1)) for i in range(N)]
            rows.append([o[i] for i in S][:-1] if False else [o[i] for i in S])
            use[kk] += 1
        # restrict to directions in R^S modulo 1_S: project out the all-ones direction
        M = sp.Matrix(rows) if rows else sp.zeros(0, k)
        if rows:
            P = sp.eye(k) - sp.ones(k, k)/k
            r = (M*P).rank()
        else:
            r = 0
        need = -(-k//2) - 1
        print(S, 'Z=', Z, 'rank', r, 'need', need, '' if r >= need else 'VIOLATION')
print('neuron usage counts', use)
