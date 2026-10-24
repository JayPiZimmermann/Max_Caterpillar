"""EXACT check (Fractions): the star family covers every k-locality, k>=3, for the
braid first layer.  Star (c, s): g = sum_{o != c} s_o sigma(x_o - x_c), s in {+1,-1}.
Centers c in 0..N-3, codes s_o = (-1)^{bit b of rank(o)} for b < ceil(log2(N-1)).
Pass test = cone rows vanish (braidlib.cone_rows) and the CORNER-box k-th mixed
difference D(G) = sum_{S subset T} (-1)^{k-|S|} sigma(G(1_S)) of the germ is nonzero
(this is Lambda_L sigma(g)/delta for the NOTE.md stencil).
Usage: python r2_star_check.py N"""
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import ceil, log2
from braidlib import localities, cone_rows, germ, evalG, nvars
from lamstar import theta_from

def corner_D(v, wT, T):
    k = len(T); tot = Fr(0)
    for r in range(k + 1):
        for S in combinations(T, r):
            z = {t: Fr(1 if t in S else 0) for t in T}
            val = evalG(v, wT, z)
            tot += (-1) ** (k - r) * (val if val > 0 else 0)
    return tot

def star_theta(N, c, s):
    w = {}; a = [Fr(0)] * N
    for o, so in s.items():
        if o < c: w[(o, c)] = so
        else: w[(c, o)] = so; a[o] += so; a[c] -= so   # sigma(x_o-x_c)=sigma(x_c-x_o)+x_o-x_c
    kappa = [a[o] + sum(w.get((o, j), 0) for j in range(o + 1, N)) for o in range(N)]
    return theta_from(N, w, kappa)

N = int(sys.argv[1]); bits = max(1, ceil(log2(N - 1)))
fam = []
for c in range(N - 2):
    others = [o for o in range(N) if o != c]
    for b in range(bits):
        fam.append(star_theta(N, c, {o: (1 if (k >> b) & 1 else -1) for k, o in enumerate(others)}))
n = nvars(N)
for m in range(3, N + 1):
    tot = cov = 0
    for T, rho in localities(N, m):
        tot += 1
        for th in fam:
            if all(sum(r[i] * th[i] for i in range(n)) == 0 for r in cone_rows(N, T, rho)):
                if corner_D(*germ(N, T, th), T) != 0:
                    cov += 1; break
    print("N", N, "k", m, "neurons", len(fam), "localities", tot, "covered", cov, flush=True)
# sanity: max_N germ has D = +-1; a pair hinge has D = 0 for k >= 3
T = tuple(range(3)); print("control D(pair hinge, k=3) =", corner_D({t: Fr(0) for t in T}, {(0, 1): Fr(1)}, T))
