"""Count localities passed by g = sum_{o>0} w_o sigma(x_o - x_0) (braid first layer).
Uses exact cone test + exact mixed difference of sigma(germ) (necessary and sufficient for
Lambda_L sigma(g) != 0 with the centered box stencil, since g == 0 on the cone)."""
import sys
from fractions import Fraction as Fr
from braidlib import *
from math import comb, factorial
def theta_star(N, w):
    th = [Fr(0)]*nvars(N); P = pidx(N)
    # sigma(x_o - x_0) = sigma(x_0 - x_o) + x_o - x_0
    for o in range(1, N):
        th[P[(0, o)]] += w[o]; th[1+o] += w[o]; th[1] -= w[o]
    return th
N = int(sys.argv[1]); m = int(sys.argv[2])
w = [None] + [Fr((-1)**o * o) for o in range(1, N)]
th = theta_star(N, w)
tot = passed = 0
for T, rho in localities(N, m):
    tot += 1
    ok = all(sum(Fr(r[i])*th[i] for i in range(len(th))) == 0 for r in cone_rows(N, T, rho))
    if ok:
        v, wT = germ(N, T, th)
        if mixed_diff_sigma(v, wT, T) != 0: passed += 1
print("N", N, "m", m, "localities", tot, "passed", passed, "fraction", Fr(passed, tot), "m/N", Fr(m, N))
