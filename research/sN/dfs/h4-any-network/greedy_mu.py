"""Measured lower bound on mu(N,m): greedy/random search over flats.
Start from the localities a seed neuron passes, repeatedly try to add a locality L (impose
its cone rows), take a random element of the new subspace, keep it if #passes (centered
mixed difference) increases.  Exact Fractions; float only for nothing."""
import sys, random
from fractions import Fraction as Fr
from braidlib import *
N, m, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
LOC = list(localities(N, m)); n = nvars(N)
ROWS = [[[(i, x) for i, x in enumerate(r) if x] for r in cone_rows(N, T, rho)] for T, rho in LOC]
def vanish(th, k): return all(sum(x*th[i] for i, x in r) == 0 for r in ROWS[k])
GOOD = {}
def npass(th):
    c = 0; Ts = {}
    for k, (T, rho) in enumerate(LOC):
        if vanish(th, k):
            if T not in Ts: Ts[T] = mixed_diff_sigma(*germ(N, T, th), T) != 0
            c += Ts[T]
    return c
def rand_elem(S):
    rows = [[x for x in cone_rows(N, *LOC[k])] for k in S]
    rows = [r for rs in rows for r in rs]
    B = nullspace(rows, n)
    if not B: return None
    return [sum(Fr(random.randint(-6, 6))*b[i] for b in B) for i in range(n)]
best = 0; bestS = None
for it in range(iters):
    S = [random.randrange(len(LOC))]
    th = rand_elem(S); cur = npass(th) if th else 0
    improved = True
    while improved:
        improved = False
        order = list(range(len(LOC))); random.shuffle(order)
        for k in order[:60]:
            if k in S or vanish(th, k): continue
            th2 = rand_elem(S + [k])
            if th2 is None: continue
            p = npass(th2)
            if p > cur:
                S.append(k); th, cur = th2, p; improved = True; break
    if cur > best:
        best = cur; bestS = list(S)
        print("iter", it, "passes", best, "of", len(LOC), "frac", float(best/len(LOC)), flush=True)
print("N", N, "m", m, "best measured", best, "of", len(LOC))
print("seed set", [LOC[k] for k in bestS])
