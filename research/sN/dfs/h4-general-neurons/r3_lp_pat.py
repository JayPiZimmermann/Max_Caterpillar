"""Round 3.  MEASURED: sparse expansion of max_N inside the labelled atoms of a list of
Wang-Basu-type patterns (all injective letter maps), by iteratively reweighted L1
(HiGHS) on random Gaussian points; saves the support in r3_lp.py's npz format so that
r3_cert.py can certify it exactly.
Usage: python r3_lp_pat.py N npts iters seed PATTERN [PATTERN ...]
   PATTERN like 11,12/11,34  (sides separated by '/', symbols = two letters each)
"""
import sys, itertools, time
import numpy as np
from scipy.optimize import linprog

N, M, iters, seed = map(int, sys.argv[1:5])
pats = [tuple(p.replace('/', ',').split(',')) for p in sys.argv[5:]]
deg = len(pats[0]) // 2
rng = np.random.default_rng(seed)
X = rng.standard_normal((M, N))
syms = [(i, i) for i in range(N)] + list(itertools.combinations(range(N), 2))
sidx = {s: k for k, s in enumerate(syms)}
mv = {s: np.maximum(X[:, s[0]], X[:, s[1]]) for s in syms}
atoms = set()
for pat in pats:
    letters = sorted(set(''.join(pat)))
    for img in itertools.permutations(range(N), len(letters)):
        f = dict(zip(letters, img))
        m = [sidx[tuple(sorted((f[s[0]], f[s[1]])))] for s in pat]
        L = tuple(sorted(m[:deg])); R = tuple(sorted(m[deg:]))
        atoms.add(tuple(sorted([L, R])))
cols, keep = [], []
for L, R in sorted(atoms):
    a = sum(mv[syms[k]] for k in L); b = sum(mv[syms[k]] for k in R)
    d = a - b
    if d.min() < -1e-12 and d.max() > 1e-12:
        cols.append(np.maximum(a, b)); keep.append((L, R))
A = np.array(cols).T
F = np.concatenate([X] + [np.maximum(X[:, i] - X[:, j], 0)[:, None] for i, j in itertools.combinations(range(N), 2)], 1)
y = X.max(1)
na, nf = A.shape[1], F.shape[1]
print('N', N, 'patterns', len(pats), 'genuine atoms', na, flush=True)
w = np.ones(na); best = None; t0 = time.time()
for it in range(iters):
    c = np.concatenate([w, w, np.zeros(nf)])
    res = linprog(c, A_eq=np.concatenate([A, -A, F], 1), b_eq=y,
                  bounds=[(0, None)] * (2 * na) + [(None, None)] * nf, method='highs')
    if res.status != 0:
        print('LP status', res.status, res.message); break
    d = res.x[:na] - res.x[na:2 * na]
    supp = np.nonzero(np.abs(d) > 1e-7)[0]
    B = np.concatenate([A[:, supp], F], 1)
    coef, *_ = np.linalg.lstsq(B, y, rcond=None)
    rel = np.linalg.norm(B @ coef - y) / np.linalg.norm(y)
    print('iter', it, 'support', len(supp), 'refit rel %.2e' % rel, '%.0fs' % (time.time() - t0), flush=True)
    if rel < 1e-9 and (best is None or len(supp) < best[0]):
        best = (len(supp), supp, d)
    w = 1.0 / (np.abs(d) + 1e-4)
supp = best[1]
print('BEST support', best[0])
for i in supp:
    L, R = keep[i]
    print('  d=%.6f' % best[2][i], [syms[s] for s in L], '|', [syms[s] for s in R])
out = 'r3_lppat_N%d_s%d.npz' % (N, seed)
np.savez(out, supp=supp, d=best[2][supp], atoms=np.array([list(keep[i][0]) + list(keep[i][1]) for i in supp]),
         syms=np.array(syms))
print('saved', out)
