"""Independent exact recomputation: star g = sum_{o!=c} s_o sigma(x_o - x_c), s in {0,+-1}.
Lambda_L sigma(g) evaluated DIRECTLY by point evaluation at p_L (T tied at 0, outside
o at -B^{rho position}), corner box of side delta, over all localities (T, rho), |T|>=3.
Exact Fractions. Usage: python r2_indep.py N"""
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations, product
sys.path.insert(0, '../h4-any-network'); from braidlib import rref
N = int(sys.argv[1]); B = Fr(10**4); dl = Fr(1, 10**6)
relu = lambda t: t if t > 0 else 0
locs = []
for k in range(3, N+1):
    for T in combinations(range(N), k):
        rest = [o for o in range(N) if o not in T]
        for rho in permutations(rest):
            p = [Fr(0)]*N
            for r, o in enumerate(rho): p[o] = -B**(r+1)
            locs.append((T, rho, p))
def lam(f, T, p):
    k = len(T); tot = Fr(0)
    for r in range(k+1):
        for S in combinations(T, r):
            x = list(p)
            for t in S: x[t] += dl
            tot += (-1)**(k-r) * f(x)
    return tot/dl
def star(c, s): return lambda x: relu(sum(so*relu(x[o]-x[c]) for o, so in s.items()))
mx = lambda x: max(x)
target = [lam(mx, T, p) for T, rho, p in locs]
assert all(t == (-1)**(len(T)+1) for t, (T, _, _) in zip(target, locs)), "target"
def fam(vals):
    F = []
    for c in range(N):
        oth = [o for o in range(N) if o != c]
        for code in product(vals, repeat=N-1):
            if any(code): F.append((c, dict(zip(oth, code))))
    return F
for name, vals in [("pm1", [1, -1]), ("pm1_0", [1, -1, 0])]:
    rows = []; rhodep = 0
    for c, s in fam(vals):
        v = [lam(star(c, s), T, p) for T, rho, p in locs]; rows.append(v)
        byT = {}
        for x, (T, rho, p) in zip(v, locs): byT.setdefault(T, set()).add(x)
        if any(len(z) > 1 for z in byT.values()): rhodep += 1
    r0 = len(rref(rows)[0]); r1 = len(rref(rows+[target])[0])
    print("N", N, name, "stars", len(rows), "localities", len(locs), "rho-dependent stars", rhodep,
          "rank", r0, "rank+target", r1, "IN SPAN" if r0 == r1 else "NOT in span", flush=True)
