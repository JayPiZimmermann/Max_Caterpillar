"""Exact certification of the covering LP  max 1.x, A x <= 1, x >= 0.

From float primal/dual solutions, round to rationals (limit_denominator),
then scale exactly into feasibility:
    x' = x / max_k (A x)_k          (primal feasible, value  = rigorous LOWER bound)
    y' = y / min_j (A^T y)_j        (dual feasible,  value  = rigorous UPPER bound)
If the two values coincide, the optimum is certified exactly.
"""
from fractions import Fraction


def certify_bounds(A, xf, yf):
    m, n = len(A), len(A[0])
    best = None
    for D in (10, 100, 1000, 10**4, 10**5, 10**6, 10**8, 10**10):
        x = [max(Fraction(0), Fraction(float(v)).limit_denominator(D)) for v in xf]
        y = [max(Fraction(0), Fraction(float(v)).limit_denominator(D)) for v in yf]
        if not any(x) or not any(y):
            continue
        Ax = max(sum(A[i][j] * x[j] for j in range(n) if x[j]) for i in range(m))
        ATy = min(sum(A[i][j] * y[i] for i in range(m) if y[i]) for j in range(n))
        if Ax <= 0 or ATy <= 0:
            continue
        x = [v / Ax for v in x]
        y = [v / ATy for v in y]
        lo, hi = sum(x), sum(y)
        if best is None or hi - lo < best[1] - best[0]:
            best = (lo, hi, x, y)
        if lo == hi:
            break
    return best
