"""Flat enumeration (mod prime p, measured) for cone-vanishing sets of braid neurons.
Prints the max number of m-localities on which one g vanishes (ignoring germ), and the
max restricted to flats where a random element has nondegenerate germs (exact check of germs
with the element lifted from small integers is NOT done here; see flats.py for exact)."""
import sys, random
from braidlib import localities, cone_rows, nvars, germ, mixed_diff_sigma
from fractions import Fraction as Fr
P = 2**61 - 1
N = int(sys.argv[1]); m = int(sys.argv[2])
LOC = list(localities(N, m)); n = nvars(N)
ROWS = [[[x % P for x in r] for r in cone_rows(N, T, rho)] for T, rho in LOC]
def rref(rows):
    M = [r[:] for r in rows]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = pow(M[r][c], P-2, P); M[r] = [x*inv % P for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(x - f*y) % P for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    return M[:r], piv
def nullspace(rows):
    R, piv = rref(rows)
    free = [c for c in range(n) if c not in piv]; B = []
    for f in free:
        v = [0]*n; v[f] = 1
        for row, pc in zip(R, piv): v[pc] = (-row[f]) % P
        B.append(v)
    return B, R, piv
def closure(B):
    return frozenset(k for k, rs in enumerate(ROWS)
        if all(sum(r[i]*b[i] for i in range(n)) % P == 0 for r in rs for b in B))
seen = {}; frontier = []
for k in range(len(LOC)):
    B, R, piv = nullspace(ROWS[k])
    F = closure(B)
    if F not in seen: seen[F] = R; frontier.append(F)
while frontier:
    new = []
    for F in frontier:
        R0 = seen[F]
        for k in range(len(LOC)):
            if k in F: continue
            B, R, piv = nullspace(R0 + ROWS[k])
            if not B: continue
            G = closure(B)
            if G not in seen: seen[G] = R; new.append(G)
    print("new flats", len(new), "total", len(seen), flush=True)
    frontier = new
sizes = sorted(((len(F), F) for F in seen), key=lambda t: -t[0])
print("N", N, "m", m, "localities", len(LOC), "flats", len(seen))
for sz, F in sizes[:8]:
    Ts = {}
    for k in F: Ts.setdefault(LOC[k][0], []).append(LOC[k][1])
    print(sz, {T: len(v) for T, v in Ts.items()})
import json
with open(f"flats_{N}_{m}_top.json", "w") as fh:
    json.dump([[LOC[k] for k in sorted(F)] for sz, F in sizes], fh)
