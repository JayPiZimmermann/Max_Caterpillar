"""Independent recheck: Lambda_L sigma(g) for star neurons g = sum_{o!=c} s_o sigma(x_o-x_c),
evaluated DIRECTLY (exact Fractions) at p_L: T at 0, outside o at -B^{rho(o)}, centered box side delta.
Vectors indexed by full localities (T, rho), not just T."""
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations, product
sys.path.insert(0, '../h4-any-network')
from braidlib import rref
relu = lambda v: v if v > 0 else 0
N = int(sys.argv[1]); B = Fr(10**6); dl = Fr(1, 10**4)
locs = []
for k in range(3, N+1):
    for T in combinations(range(N), k):
        rest = [o for o in range(N) if o not in T]
        for rho in permutations(rest):
            p = [Fr(0)]*N
            for r, o in enumerate(rho): p[o] = -B**(r+1)
            locs.append((T, rho, p))
def Lam(f, T, p):
    k = len(T); tot = Fr(0)
    for bits in range(1 << k):
        x = list(p); sg = 1
        for i, t in enumerate(T):
            if bits >> i & 1: x[t] += dl/2
            else: x[t] -= dl/2; sg = -sg
        tot += sg*f(x)
    return tot / dl
def star(c, s):
    return lambda x: relu(sum(s[o]*relu(x[o]-x[c]) for o in s))
target = [Lam(lambda x: max(x), T, p) for T, rho, p in locs]
stars = []
for c in range(N):
    others = [o for o in range(N) if o != c]
    for code in product([1, -1, 0], repeat=N-1):
        stars.append((c, dict(zip(others, code))))
rows = []; dep_rho = 0; nonzero_cnotinT = 0
for c, s in stars:
    f = star(c, s); v = [Lam(f, T, p) for T, rho, p in locs]; rows.append(v)
    byT = {}
    for (T, rho, p), val in zip(locs, v):
        byT.setdefault(T, set()).add(val)
        if c not in T and val != 0: nonzero_cnotinT += 1
    dep_rho += any(len(vs) > 1 for vs in byT.values())
print("N", N, "localities", len(locs), "stars", len(stars))
print("stars whose Lambda depends on rho:", dep_rho, " nonzero entries with c notin T:", nonzero_cnotinT)
for name, sel in [("pm1", lambda s: 0 not in s.values()), ("pm1_0", lambda s: True)]:
    R = [r for (c, s), r in zip(stars, rows) if sel(s)]
    r0 = len(rref(R)[0]); r1 = len(rref(R + [target])[0])
    print(name, "rank", r0, "rank+target", r1, "IN SPAN" if r0 == r1 else "NOT in span", flush=True)
