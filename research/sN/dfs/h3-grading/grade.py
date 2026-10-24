"""For Young subgroup S_mu and twist (triv/sgn): ranks of the nested families
A_N, A_N + {U_k : |M_k| <= j-1} (polytope dim <= j), j = 1..N-1, restricted to
H-invariant (twisted) orbit sums.  Usage: grade.py N mu twist npts_extra seed"""
import sys, json, time
import numpy as np
from common import keys
from sym import *
N = int(sys.argv[1]); mu = tuple(int(c) for c in sys.argv[2]); tw = sys.argv[3]
extra = int(sys.argv[4]) if len(sys.argv) > 4 else 40; seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
t0 = time.time()
ks = keys(N); auxs = vs.aux_functions(N)
gens = young_gens(N, mu)
kor = orbits(ks, act_key, gens)
def keep(o):
    return tw == 'triv' or not o[1]
# exactly invariant spanning family of A_N: relu(+-x_i), relu(x_i - x_j) for all ordered i != j
auxs = [('pos', i) for i in range(N)] + [('neg', i) for i in range(N)] + \
       [('pair', i, j) for i in range(N) for j in range(N) if i != j]
def act_aux_exact(g, a):
    return (a[0], g[a[1]]) if a[0] != 'pair' else ('pair', g[a[1]], g[a[2]])
aor = orbits(auxs, act_aux_exact, gens)
aor = [o for o in aor if keep(o)]
kor = [o for o in kor if keep(o)]
ncols = len(kor) + len(aor)
rng = np.random.default_rng(seed)
npts = ncols + extra
X = rng.integers(-10**4, 10**4, size=(npts, N), endpoint=True).astype(np.int64)
kidx = {k: n for n, k in enumerate(ks)}
EK = eval_keys(ks, X)
EA = eval_aux(auxs, X)
aidx = {a: n for n, a in enumerate(auxs)}
sgnf = (lambda s: s) if tw == 'sgn' else (lambda s: 1)
Arows = [sum(sgnf(s) * EA[aidx[a]] for a, s in o.items()) for o, _ in aor]
blocks = [np.array(Arows, dtype=np.int64).reshape(-1, npts)]
dims = sorted({len(k[1]) for k in ks})
for m in dims:
    rows = [sum(sgnf(s) * EK[kidx[k]] for k, s in o.items()) for o, _ in kor if len(next(iter(o))[1]) == m]
    blocks.append(np.array(rows, dtype=np.int64).reshape(-1, npts))
r = run_rank(blocks, f'{N}_{"".join(map(str,mu))}_{tw}_{seed}')
print(json.dumps({'N': N, 'mu': mu, 'twist': tw, 'seed': seed, 'npts': npts,
                  'ncols': [b.shape[0] for b in blocks], 'ranks_A_then_by_M': r,
                  'secs': round(time.time() - t0, 1)}), flush=True)
