"""Q1: is there one g (braid first layer, real weights) vanishing on every m-locality cone,
and if so, are its germs non-degenerate (mixed difference of sigma(G) nonzero)?"""
import sys, random
from fractions import Fraction as Fr
from braidlib import *
N = int(sys.argv[1]); m = int(sys.argv[2]) if len(sys.argv) > 2 else 3
rows = []
for T, rho in localities(N, m):
    rows += cone_rows(N, T, rho)
B = nullspace(rows, nvars(N))
print("N", N, "m", m, "vars", nvars(N), "nullity", len(B))
random.seed(1)
for trial in range(3):
    th = [sum(Fr(random.randint(-9, 9))*b[i] for b in B) for i in range(nvars(N))]
    bad = 0
    for T in combinations(range(N), m):
        v, wT = germ(N, T, th)
        if mixed_diff_sigma(v, wT, T) == 0: bad += 1
    print("trial", trial, "localities-T with zero mixed difference:", bad, "of", len(list(combinations(range(N), m))))
for b in B:
    print([str(x) for x in b])
