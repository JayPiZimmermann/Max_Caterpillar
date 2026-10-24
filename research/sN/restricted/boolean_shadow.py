"""EXACT: the Boolean shadow of the restricted model is weak.
Necessary condition (proved): OR_N(S) = sum_k d_k relu(f_k(S)) + q(S) on {0,1}^N
with f_k, q quadratic set functions.  Symmetric choice f_r(S) = |S|(r-|S|),
r = 2..N: check (sympy-free, Fractions) that OR_N lies in span{m, m^2, relu(m(r-m))}
as functions of m = |S| in 0..N.  So the shadow alone gives at most N-1."""
from fractions import Fraction
import sys

def solve(rows, rhs):
    # exact least-squares-free consistency check by Gaussian elimination
    A = [list(map(Fraction, r)) + [Fraction(b)] for r, b in zip(rows, rhs)]
    n = len(A[0]) - 1; piv = 0
    for c in range(n):
        p = next((i for i in range(piv, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[piv], A[p] = A[p], A[piv]
        for i in range(len(A)):
            if i != piv and A[i][c] != 0:
                t = A[i][c] / A[piv][c]
                A[i] = [x - t * y for x, y in zip(A[i], A[piv])]
        piv += 1
    return all(any(x != 0 for x in r[:-1]) or r[-1] == 0 for r in A)

for N in range(3, int(sys.argv[1]) + 1):
    rows = [[m, m * m] + [max(m * (r - m), 0) for r in range(2, N + 1)] for m in range(N + 1)]
    rhs = [1 if m else 0 for m in range(N + 1)]
    print(N, 'OR in span with', N - 1, 'symmetric relu terms:', solve(rows, rhs))
