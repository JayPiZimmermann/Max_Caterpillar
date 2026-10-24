"""Multiplicity m_lam of the irreducible S_N-module S^lam in V_N (and graded prefixes) as
dim(a_T b_T V): a_T = sum over row group R, b_T = signed sum over column group C of the
row-reading tableau T of shape lam.  Columns: b_T applied to C-orbit representatives
(signed orbit sums; orbits with an odd stabilizer element vanish); rows: points x_p, the
value of a_T F at x_p is sum_{r in R} F(r x_p).  Ranks mod p are lower bounds (measured).
Usage: ysym.py N lam [extra seed]"""
import sys, json, time, itertools
import numpy as np
from common import keys
from sym import act_key, orbits, eval_keys, run_rank
N = int(sys.argv[1]); lam = tuple(int(c) for c in sys.argv[2])
extra = int(sys.argv[3]) if len(sys.argv) > 3 else 30; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
npts_override = int(sys.argv[5]) if len(sys.argv) > 5 else None
t0 = time.time()
ks = keys(N)
aux = []
for i in range(N):
    for s in (1, -1):
        e = [0] * N; e[i] = s; aux.append((tuple(e), frozenset()))
for i in range(N):
    for j in range(N):
        if i != j:
            e = [0] * N; e[i] = 1; e[j] = -1; aux.append((tuple(e), frozenset()))
fam = aux + ks
grade = [-1] * len(aux) + [len(k[1]) for k in ks]
rows, s = [], 0
for l in lam:
    rows.append(list(range(s, s + l))); s += l
cols = [[r[j] for r in rows if len(r) > j] for j in range(lam[0])]
def transp(a, b):
    g = list(range(N)); g[a], g[b] = g[b], g[a]; return tuple(g)
cgens = [transp(c[0], c[t]) for c in cols for t in range(1, len(c))]
Rel = [()]
Rgroup = []
for perms in itertools.product(*[itertools.permutations(r) for r in rows]):
    g = list(range(N))
    for r, pr in zip(rows, perms):
        for a, b in zip(r, pr): g[a] = b
    Rgroup.append(g)
orbs = [o for o, odd in orbits(fam, act_key, cgens) if not odd]
fidx = {k: n for n, k in enumerate(fam)}
orbs.sort(key=lambda o: grade[fidx[next(iter(o))]])
grades = sorted({grade[fidx[next(iter(o))]] for o in orbs})
nc = len(orbs)
# number of points: m_lam <= nc; use enough points
npts = npts_override or (nc + extra)
rng = np.random.default_rng(seed)
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
M = np.zeros((nc, npts), dtype=np.int64)
# member lists
mem_idx = [np.array([fidx[k] for k in o]) for o in orbs]
mem_sgn = [np.array([o[k] for k in o]) for o in orbs]
P = 2147483647
for g in Rgroup:
    Y = X[:, g]                        # coordinates permuted: y_i = x_{g(i)}
    E = eval_keys(fam, Y) % P          # (len(fam), npts)
    for c in range(nc):
        M[c] = (M[c] + (mem_sgn[c][:, None] * E[mem_idx[c]]).sum(axis=0)) % P
blocks, bounds = [], []
for gr in grades:
    sel = [c for c in range(nc) if grade[fidx[next(iter(orbs[c]))]] == gr]
    blocks.append(M[sel])
r = run_rank(blocks, f'ys{N}_{"".join(map(str,lam))}_{seed}')
print(json.dumps({'N': N, 'lam': lam, 'grades': grades, 'ncols': nc, 'npts': npts, '|R|': len(Rgroup),
                  'mult_prefix': r, 'saturated': r[-1] >= npts, 'secs': round(time.time() - t0, 1)}), flush=True)
