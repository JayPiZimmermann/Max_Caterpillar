"""Pair-killing certificate over a SUPERSET of germs: all (v, M) on m=4 variables with
sum v = 0, |v_t| <= V, M any set of pairs (i<j) [normalized], full (every variable used).
For every pair of such germs, is there a mixed 4th difference D (bases (0,a1..a3), a in
[-B,B], steps c in CV^4) with D max != 0 killing both?  usage: superset.py V B cvals"""
import sys, itertools
import numpy as np
V, B = int(sys.argv[1]), int(sys.argv[2]); CV = [int(x) for x in sys.argv[3].split(',')]
m = 4
pairs = [(i, j) for i in range(m) for j in range(i + 1, m)]
germs = []
for v in itertools.product(range(-V, V + 1), repeat=m):
    if sum(v): continue
    for r in range(len(pairs) + 1):
        for M in itertools.combinations(pairs, r):
            if all(v[t] != 0 or any(t in e for e in M) for t in range(m)):
                germs.append((v, M))
print('superset full germs', len(germs), flush=True)
# grid evaluation
lo, hi = -B, B + max(CV)
rng = np.arange(lo, hi + 1)
grid = np.array(np.meshgrid(*([np.arange(0, max(CV) + 1)] + [rng] * (m - 1)), indexing='ij')).reshape(m, -1).T
def idx(p):
    return ((p[..., 0]) * len(rng) ** 3 + (p[..., 1] - lo) * len(rng) ** 2 + (p[..., 2] - lo) * len(rng) + (p[..., 3] - lo))
vals = np.zeros((len(germs), len(grid)), dtype=np.int64)
for k, (v, M) in enumerate(germs):
    a = grid @ np.array(v)
    for i, j in M:
        a = a + np.maximum(grid[:, i] - grid[:, j], 0)
    vals[k] = np.maximum(a, 0)
mx = grid.max(1)
funcs = []
for a in itertools.product(range(-B, B + 1), repeat=m - 1):
    base = np.array((0,) + a)
    for c in itertools.product(CV, repeat=m):
        pts = []; sg = []
        for S in range(1 << m):
            p = base.copy()
            for i in range(m):
                if S >> i & 1: p[i] += c[i]
            pts.append(p); sg.append((-1) ** (m - bin(S).count('1')))
        pts = np.array(pts); ii = idx(pts); sg = np.array(sg)
        if (sg * mx[ii]).sum() == 0: continue
        funcs.append(((0,) + a, c, ii, sg))
print('functionals', len(funcs), flush=True)
K = np.zeros((len(germs), len(funcs)), dtype=bool)   # K[g,f]: f kills g
for f, (_, _, ii, sg) in enumerate(funcs):
    K[:, f] = (vals[:, ii] @ sg) == 0
Kp = np.packbits(K, axis=1)
bad = 0; ex = []
for g in range(len(germs)):
    inter = np.bitwise_and(Kp[g][None, :], Kp[g:])
    ok = inter.any(1)
    nb = (~ok).sum()
    if nb:
        bad += nb
        if len(ex) < 10:
            for h in np.nonzero(~ok)[0][:3]:
                ex.append((germs[g], germs[g + h]))
print('pairs (incl. g=g) not killed:', bad)
for e in ex[:10]: print('  ', e)
