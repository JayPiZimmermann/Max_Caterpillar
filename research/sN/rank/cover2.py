"""Best stencil certificate for the local sparsity s'_m on the computed germ class:
s'_m >= min #full germs whose hit sets H_g = {stencils D: D g != 0} cover all stencils
with D max != 0 (a set not covering is killed by some D, contradiction).
Set-cover ILP (0/1 data, HiGHS) and its LP relaxation.
usage: cover.py m N B cvals"""
import sys, itertools, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds, linprog
from germs import localities, relabel
m, N, B = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
CV = [int(x) for x in sys.argv[4].split(',')]
def isfull(g):
    h, M = g
    return all(h[t] != 0 or any(t in e for e in M) for t in range(len(h)))
G = {g for *_, g in localities(N, m)}
Gc = {relabel(g, p) for g in G for p in itertools.permutations(range(m))}
full = sorted([g for g in Gc if isfull(g)], key=str)
lo, hi = -B, B + max(CV); n1 = hi - lo + 1
axes = [np.arange(0, max(CV) + 1)] + [np.arange(lo, hi + 1)] * (m - 1)
grid = np.array(np.meshgrid(*axes, indexing='ij')).reshape(m, -1).T
def idx(p):
    r = p[..., 0]
    for i in range(1, m):
        r = r * n1 + (p[..., i] - lo)
    return r
vals = np.zeros((len(full), len(grid)), dtype=np.int64)
for k, (v, M) in enumerate(full):
    a = grid @ np.array(v)
    for i, j in M:
        a = a + np.maximum(grid[:, i] - grid[:, j], 0)
    vals[k] = np.maximum(a, 0)
mx = grid.max(1)
H = set()
subs = list(range(1 << m)); sg = np.array([(-1) ** (m - bin(S).count('1')) for S in subs])
bits = np.array([[S >> i & 1 for i in range(m)] for S in subs])
stencils = [(np.array((0,) + a), np.array(c)) for a in itertools.product(range(-B, B + 1), repeat=m - 1)
            for c in itertools.product(CV, repeat=m)]
CH = 400
for s0 in range(0, len(stencils), CH):
    ch = stencils[s0:s0 + CH]
    pts = np.array([b[None, :] + bits * c[None, :] for b, c in ch])     # (ch, 2^m, m)
    ii = idx(pts)                                                       # (ch, 2^m)
    dm = (mx[ii] * sg[None, :]).sum(1)
    D = np.einsum('gcs,s->gc', vals[:, ii], sg)                         # (germs, ch)
    for j in np.nonzero(dm)[0]:
        H.add(np.packbits(D[:, j] != 0).tobytes())
H = [np.unpackbits(np.frombuffer(h, dtype=np.uint8))[:len(full)].astype(bool) for h in H]
H = np.unique(np.array(H), axis=0)          # rows: stencils, cols: germs
print(f'm={m} N={N}: full germs {len(full)}, distinct stencil patterns {len(H)}', flush=True)
A = H.astype(float)
lp = linprog(np.ones(len(full)), A_ub=-A, b_ub=-np.ones(len(H)), bounds=[(0, 1)] * len(full), method='highs')
print('LP cover lower bound', lp.fun, flush=True)
t0 = time.time()
res = milp(np.ones(len(full)), constraints=LinearConstraint(A, lb=np.ones(len(H)), ub=np.inf),
           integrality=np.ones(len(full)), bounds=Bounds(0, 1), options={'time_limit': 1200})
print('ILP cover number', res.fun, res.status, res.message, f'{time.time()-t0:.0f}s')
if res.x is not None:
    print('  cover:', [full[i] for i in np.nonzero(res.x > 0.5)[0]])
