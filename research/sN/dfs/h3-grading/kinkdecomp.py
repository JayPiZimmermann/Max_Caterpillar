"""Non-braid kink decomposition.  kappa: V -> (+)_{cells C, primitive d not braid} R, kink of f on
d-perp inside C.  ker kappa = V cap B.  Compare rank(kappa) with sum_d rank(kappa_d).
Exact ranks over Q via Fraction-free modular rank of integer matrices (lower bound) -- measured."""
import sys, itertools, collections
import numpy as np
from common import keys, vs
from sym import run_rank
N = int(sys.argv[1])
ks = keys(N)
funcs = [('key', k) for k in ks]
def braid(d):
    nz = [t for t in d if t]
    return (len(nz) == 1 and abs(nz[0]) == 1) or (sorted(nz) == [-1, 1])
rows = collections.defaultdict(list)   # d -> list of row dicts
for order in vs.cells(N):
    rays = vs.cell_rays(N, order); pos = vs.cell_rank(N, order)
    kd = {}
    for idx, f in enumerate(funcs):
        kk, lin = vs.coordinates_of(N, order, rays, pos, f)
        for d, c in kk.items():
            if not braid(d):
                kd.setdefault(d, {})[idx] = c
    for d, r in kd.items():
        rows[d].append(r)
def tomat(rs):
    M = np.zeros((len(rs), len(funcs)), dtype=np.int64)
    for i, r in enumerate(rs):
        for j, c in r.items(): M[i, j] = c
    return M
allrows = [r for d in rows for r in rows[d]]
# rank of kappa = rank of the row space; run_rank works on vectors = rows (dim = #funcs)
rk = run_rank([tomat(allrows)], f'kink{N}')[0]
per = {d: run_rank([tomat(rows[d])], f'kinkd{N}')[0] for d in rows}
# classes up to S_N and sign
def canon(d):
    return min(min(tuple(sorted(d))), tuple(sorted(-t for t in d)))
cls = collections.defaultdict(list)
for d, r in per.items():
    cls[tuple(sorted(d))].append(r)
print(f'N={N} non-braid directions {len(rows)}  rank kappa {rk}  sum_d rank kappa_d {sum(per.values())}')
for c in sorted(cls):
    print('  d multiset', c, 'count', len(cls[c]), 'ranks', sorted(collections.Counter(cls[c]).items()))
