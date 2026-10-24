"""Local (codimension-2) model of gr_1.  For a grade-1 key (h,{(i,j)}) the singular locus contains the
flat L = W^perp, W = span(h, e_i - e_j).  Since h.x0 = (e_i-e_j).x0 = 0 on L, U(x0 + z) = U(z), so the
transverse germ is z -> U(z) restricted to the plane W itself (W is transversal to L = W^perp).  For each W:
loc_W = rank{germs of grade-1 keys with span W} modulo {linear, germs sigma(l.z) for l in W among
aux directions and |M|=0 heads}.  Prediction: dim gr_1 = sum_W loc_W (if the localisation map
gr_1 -> (+)_W loc_W is injective).  Mod-p ranks of exact integer evaluations (measured)."""
import sys, collections
import numpy as np
from common import keys
from sym import eval_keys, run_rank
from flats import rref
N = int(sys.argv[1]); ks = keys(N)
rng = np.random.default_rng(11)
y = rng.integers(-1000, 1000, size=(2, N))
st = rng.integers(-10**4, 10**4, size=(400, 2))
lines = []
for i in range(N):
    e = [0] * N; e[i] = 1; lines.append(tuple(e))
    for j in range(N):
        if i != j:
            e = [0] * N; e[i] = 1; e[j] = -1; lines.append(tuple(e))
lines += [k[0] for k in ks if not k[1]]
def span(vs):
    return rref([list(v) for v in vs])
def inW(l, W):
    return len(rref([list(r) for r in W] + [list(l)])) == len(W)
byW = collections.defaultdict(list)
for k in ks:
    if len(k[1]) == 1:
        (i, j), = k[1]; d = [0] * N; d[i] = 1; d[j] = -1
        byW[span([k[0], d])].append(k)
tot = 0; hist = collections.Counter()
for n, (W, kk) in enumerate(byW.items()):
    (i, j), = kk[0][1]; d = [0] * N; d[i] = 1; d[j] = -1
    X = st @ np.array([kk[0][0], d], dtype=np.int64)     # points z = s h + t d in W
    ls = [l for l in lines if inW(l, W)]
    base = np.concatenate([X.T.astype(np.int64), eval_keys([(l, frozenset()) for l in ls], X)]) if ls else X.T.astype(np.int64)
    r = run_rank([base, eval_keys(kk, X)], f'loc1_{N}')
    tot += r[1] - r[0]; hist[(len(kk), r[1] - r[0])] += 1
print(f'N={N} spans {len(byW)} predicted dim gr_1 = {tot}; (#keys, loc) histogram {sorted(hist.items())}')
# new kink hyperplanes: lines h, h + e_i - e_j of grade-1 keys not among aux / |M|=0 heads (up to sign)
def canon(l):
    g = np.gcd.reduce(np.abs(l)); l = tuple(int(t // g) for t in l)
    return max(l, tuple(-t for t in l))
old = {canon(np.array(l)) for l in lines}
new = set()
for k in ks:
    if len(k[1]) == 1:
        (i, j), = k[1]; h = np.array(k[0])
        d = np.zeros(N, dtype=int); d[i] = 1; d[j] = -1
        for l in (h, h + d):
            if np.any(l): 
                c = canon(l)
                if c not in old: new.add(c)
print(f'N={N} new kink lines from grade-1 keys: {len(new)}; local prediction + new lines = {tot + len(new)}')
