"""Exact max number of m-localities passed by one braid-first-layer neuron.
Enumerates all flats of the arrangement {ker(cone_rows(L))} (closed locality sets),
and for each flat counts localities whose T admits a good germ for some element (upper
bound, 'ub') and for random elements (lower bound, 'lb')."""
import sys, random
from fractions import Fraction as Fr
from braidlib import *
N = int(sys.argv[1]); m = int(sys.argv[2])
LOC = list(localities(N, m)); n = nvars(N)
ROWS = [cone_rows(N, T, rho) for T, rho in LOC]
def closure(B):
    return frozenset(k for k, rs in enumerate(ROWS)
                     if all(sum(r[i]*b[i] for i in range(n)) == 0 for r in rs for b in B))
cache = {}
def flat_of(S):
    rows = [r for k in S for r in ROWS[k]]
    B = nullspace(rows, n)
    return closure(B), B
random.seed(0)
def score(F, B):
    if not B: return 0, 0
    Ts = sorted(set(LOC[k][0] for k in F))
    good = set()
    best = 0
    for trial in range(12):
        th = [sum(Fr(random.randint(-20, 20))*b[i] for b in B) for i in range(n)]
        g = set(T for T in Ts if mixed_diff_sigma(*germ(N, T, th), T) != 0)
        good |= g
        best = max(best, sum(1 for k in F if LOC[k][0] in g))
    ub = sum(1 for k in F if LOC[k][0] in good)
    return best, ub
seen = {}
frontier = []
for k in range(len(LOC)):
    F, B = flat_of({k})
    if F not in seen and B:
        seen[F] = B; frontier.append(F)
level = 1
while frontier:
    new = []
    for F in frontier:
        for k in range(len(LOC)):
            if k in F: continue
            G, B = flat_of(F | {k})
            if B and G not in seen:
                seen[G] = B; new.append(G)
    level += 1
    print("level", level, "new flats", len(new), "total", len(seen), flush=True)
    frontier = new
res = [(score(F, B), len(F), F) for F, B in seen.items()]
lbmax = max(r[0][0] for r in res); ubmax = max(r[0][1] for r in res)
print("N", N, "m", m, "localities", len(LOC), "max passed lb", lbmax, "ub", ubmax)
for (lb, ub), sz, F in sorted(res, key=lambda r: -r[0][1])[:5]:
    print(lb, ub, sz, sorted(LOC[k] for k in F))
