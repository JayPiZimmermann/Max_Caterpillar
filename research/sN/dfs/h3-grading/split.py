"""Hyperplane-splitting test for V_N modulo linear functions.
Every f in V_N is positively homogeneous PL; f mod linear functions is determined by its jump
functions J_u f : u^perp -> R, J_u f(y) = f(y+tu)+f(y-tu)-2f(y) (t>0 small, y generic in u^perp).
Hence dim V_N/lin <= sum_u r_u, r_u = dim span{J_u f : f in V_N}, with equality iff
V_N/lin = (+)_u (its image in direction u)  ("splitting").
Instrument: for each candidate kink normal u (primitive; from inner hinges e_i-e_j and outer normals
h + sum_{S} (e_i-e_j), S subset M), sample integer y in u^perp scaled by R, take t = 1,
rank mod p of the exact integer second differences.  Rank is a lower bound for r_u (measured;
sampling may miss regions of u^perp).  Usage: split.py N [pts_extra] [seed]"""
import sys, itertools, collections, json, time
import numpy as np
from math import gcd
from common import keys
from sym import eval_keys
P = 2147483647
N = int(sys.argv[1]); extra = int(sys.argv[2]) if len(sys.argv) > 2 else 30
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
t0 = time.time()
ks = keys(N)
aux = []
for i in range(N):
    e = [0] * N; e[i] = 1; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(i + 1, N):
        e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
fam = aux + ks
def canon(v):
    g = 0
    for t in v: g = gcd(g, abs(t))
    if g == 0: return None
    v = tuple(t // g for t in v)
    nz = next(t for t in v if t)
    return v if nz > 0 else tuple(-t for t in v)
def dvec(i, j):
    e = [0] * N; e[i] = 1; e[j] = -1; return e
bylines = collections.defaultdict(list)
for n, (h, M) in enumerate(fam):
    Ml = sorted(M); cand = set()
    for (i, j) in Ml: cand.add(canon(dvec(i, j)))
    for r in range(len(Ml) + 1):
        for S in itertools.combinations(Ml, r):
            v = list(h)
            for (i, j) in S: v[i] += 1; v[j] -= 1
            c = canon(v)
            if c: cand.add(c)
    for c in cand: bylines[c].append(n)
def rank_mod_p(A):
    A = A % P; r = 0; rows, cols = A.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i, c]), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        nzr = np.nonzero(A[:, c])[0]
        for i in nzr:
            if i != r: A[i] = (A[i] - A[i, c] * A[r]) % P
        r += 1
        if r == rows: break
    return r
rng = np.random.default_rng(seed)
R = 10 ** 4
tot = 0; hist = collections.Counter(); per = {}
for u, fl in bylines.items():
    uu = np.array(u, dtype=np.int64)
    npts = len(fl) + extra
    Z = rng.integers(-R, R, size=(npts, N), endpoint=True)
    Y = (uu @ uu) * Z - np.outer(Z @ uu, uu)          # integer points of u^perp
    Y *= 50
    F = [fam[n] for n in fl]
    E = eval_keys(F, Y + uu) + eval_keys(F, Y - uu) - 2 * eval_keys(F, Y)
    r = rank_mod_p(E.T.copy())
    per[str(u)] = (len(fl), r)
    tot += r; hist[(sum(1 for t in u if t), r)] += 1
print(json.dumps({'N': N, 'seed': seed, 'extra': extra, 'nlines': len(bylines), 'sum_r_u': tot,
                  'nonzero_lines': sum(1 for v in per.values() if v[1]), 'secs': round(time.time() - t0, 1)}))
