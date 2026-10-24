"""Measured span test (random integer points, rank mod p): is max_N in the span of a
family of braid-first-layer second-layer neurons plus the braid 1HL functions?
Family 'star': sigma(sum_{o!=c} s_o sigma(x_o-x_c)), s in {-1,0,1}^(N-1).
Family 'star2': coefficients in {-2..2}.  Rank equality => (measured) membership."""
import sys, random, itertools
import numpy as np
P = 2_147_483_629
def relu(t): return t if t > 0 else 0
def rank_mod_p(M):
    M = [list(r) for r in M]; rk = 0; ncol = len(M[0])
    for c in range(ncol):
        p = next((i for i in range(rk, len(M)) if M[i][c] % P), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        inv = pow(M[rk][c], P-2, P); M[rk] = [x*inv % P for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % P:
                f = M[i][c]; M[i] = [(x - f*y) % P for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk
N = int(sys.argv[1]); fam = sys.argv[2]
vals = {"star": [-1, 0, 1], "star2": [-2, -1, 0, 1, 2]}[fam]
funcs = []
for i in range(N): funcs.append(lambda x, i=i: x[i])
for i, j in itertools.combinations(range(N), 2): funcs.append(lambda x, i=i, j=j: relu(x[i]-x[j]))
base = len(funcs)
seen = set()
for c in range(N):
    others = [o for o in range(N) if o != c]
    for s in itertools.product(vals, repeat=N-1):
        if all(v == 0 for v in s): continue
        g = tuple(sorted(zip(others, s)))
        funcs.append(lambda x, c=c, g=g: relu(sum(v*relu(x[o]-x[c]) for o, v in g)))
funcs.append(lambda x: 1)
nf = len(funcs)
random.seed(3)
npts = nf + 80
pts = [[random.randint(-10**5, 10**5) for _ in range(N)] for _ in range(npts)]
M = [[f(x) % P for x in pts] for f in funcs]
r0 = rank_mod_p(M)
r1 = rank_mod_p(M + [[max(x) % P for x in pts]])
print("N", N, "family", fam, "functions", nf, "rank", r0, "rank with max", r1, "-> max in span (measured)" if r0 == r1 else "-> max NOT in span (rank lower bound certified)")
