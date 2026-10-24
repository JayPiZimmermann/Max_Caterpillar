"""Independent exact recomputation: Lambda_L sigma(g) for star neurons
g = sum_{o!=c} s_o sigma(x_o - x_c), s in {0,+-1}, evaluated DIRECTLY from the network
function at p_L (p_t = 0 for t in T, p_o = -B^{rank}) with a k-th mixed difference
in the T coordinates (corner box [0,d]^T, or centered box). Index set: all (T, rho), |T|>=3.
Usage: python star_rho.py N [corner|center]"""
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations, product
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-any-network')
from braidlib import rref
N = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else 'corner'
B = 10; d = Fr(1, 1000)
sig = lambda x: x if x > 0 else 0
locs = []
for k in range(3, N + 1):
    for T in combinations(range(N), k):
        rest = [o for o in range(N) if o not in T]
        for rho in permutations(rest):
            p = [Fr(0)] * N
            for r, o in enumerate(rho): p[o] = -Fr(B) ** (r + 1)
            locs.append((T, rho, p))
def Lam(f, T, p):
    k = len(T); tot = Fr(0)
    off = Fr(0) if mode == 'corner' else -d / 2
    for bits in product([0, 1], repeat=k):
        x = list(p)
        for t, b in zip(T, bits): x[t] += off + b * d
        tot += (-1) ** (k - sum(bits)) * f(x)
    return tot / d          # normalise (homogeneous germ)
def star(c, s):
    return lambda x: sig(sum(so * sig(x[o] - x[c]) for o, so in s.items()))
mx = lambda x: max(x)
target = [Lam(mx, T, p) for T, rho, p in locs]
rows = []; rho_dep = 0
for c in range(N):
    others = [o for o in range(N) if o != c]
    for code in product([1, -1, 0], repeat=N - 1):
        f = star(c, dict(zip(others, code)))
        rows.append([Lam(f, T, p) for T, rho, p in locs])
# rho-dependence: same T, different rho, different value
for r in rows:
    byT = {}
    for (T, rho, p), v in zip(locs, r): byT.setdefault(T, set()).add(v)
    if any(len(v) > 1 for v in byT.values()): rho_dep += 1
r0 = len(rref(rows)[0]); r1 = len(rref(rows + [target])[0])
print("N", N, mode, "localities", len(locs), "stars", len(rows), "stars with rho-dependent Lambda", rho_dep,
      "rank", r0, "rank+target", r1, "IN SPAN" if r0 == r1 else "NOT in span", flush=True)
print("target distinct values", sorted(set(target)))
