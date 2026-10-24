"""Star gadget: Gamma = sum_{theta subset [m]} (-1)^|theta| sigma(g0 + sum_{o in theta} sigma(x_a - x_o)).
On an a-max chamber with z_(1)<...<z_(m) (z_o = x_a - x_o), g0 = sum_j gamma_j z_(j).
Need: for all theta, R(theta)_i = Gamma_i + |theta cap [i,m]| one-signed (Gamma_i = suffix sums of gamma).
Then Gamma = kappa * sigma(x_a - max_{o}x_o) globally; kappa = coefficient of eps_1."""
import itertools, sys
from fractions import Fraction as Fr
def check(gamma):
    m = len(gamma)
    G = [sum(gamma[i:]) for i in range(m)]
    val = [Fr(0)] * m
    for k in range(m + 1):
        for th in itertools.combinations(range(m), k):
            R = [G[i] + sum(1 for j in th if j >= i) for i in range(m)]
            if any(r > 0 for r in R) and any(r < 0 for r in R): return None
            if any(r > 0 for r in R):
                for i in range(m): val[i] += (-1) ** k * R[i]
    return val
m = int(sys.argv[1]); D = int(sys.argv[2]) if len(sys.argv) > 2 else 6
found = []
for pn in range(-4 * D * m, 4 * D + 1):
    for qn in range(-2 * D, 2 * D + 1):
        p, q = Fr(pn, D), Fr(qn, D)
        gamma = [p + q * (j + 1) for j in range(m)]
        v = check(gamma)
        if v is not None and any(v):
            found.append((p, q, v))
print('m', m, 'solutions', len(found))
for p, q, v in found[:10]: print('p', p, 'q', q, 'value', [str(x) for x in v])
