"""For each key (h, M): its normal space W_k = span(h, e_i - e_j : (i,j) in M) (dim |M|+1 = dim Q_k,
the linear span of the polytope Q_k).  Count distinct W_k per grade |M| (exact rational RREF)."""
import sys, collections
from fractions import Fraction
from common import keys
def rref(rows):
    A = [[Fraction(x) for x in r] for r in rows]; out = []; c = 0; n = len(A[0])
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        piv = A[r][c]; A[r] = [x / piv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == len(A): break
    return tuple(tuple(x) for x in A[:r])
for N in map(int, sys.argv[1:]):
    ks = keys(N)
    per = collections.defaultdict(set)
    for h, M in ks:
        rows = [list(h)]
        for i, j in M:
            e = [0] * N; e[i] = 1; e[j] = -1; rows.append(e)
        W = rref(rows)
        assert len(W) == len(M) + 1
        per[len(M)].add(W)
    print(N, 'distinct spans per |M|:', [len(per[m]) for m in sorted(per)], flush=True)
