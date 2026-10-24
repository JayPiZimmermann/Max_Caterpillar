#!/usr/bin/env python3
"""Generic symmetric tests for a cached germ family (research/sN/trees, step 13).
T f = sum_{delta in S_m-orbit(p)} MD_delta f, p a multiset of large random step values with a prescribed
multiplicity shape (small orbits).  Tests are added in batches until the rank of the family saturates;
then max is tested.  Usage: sym_generic.py famfile m batch nbatches [seed]"""
import sys, itertools, pickle, time
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import eval_germ, orbit, rank_mod_p, P

ff, m, B, NB = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 7
fam = pickle.load(open(ff, 'rb'))
rng = np.random.default_rng(seed)
cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=np.int64)
shapes = {7: [(3, 2, 1, 1), (4, 2, 1), (3, 3, 1), (2, 2, 2, 1), (3, 2, 2), (4, 1, 1, 1), (5, 1, 1)],
          6: [(2, 2, 1, 1), (3, 1, 1, 1), (2, 2, 2), (3, 2, 1), (2, 1, 1, 1, 1)],
          5: [(2, 1, 1, 1), (2, 2, 1), (3, 1, 1), (1, 1, 1, 1, 1)]}[m]
rows = []; brow = []
t0 = time.time()
for bt in range(NB):
    pats = []
    for _ in range(B):
        sh = shapes[rng.integers(len(shapes))]
        vals = rng.choice(np.arange(1, 10**6), size=len(sh), replace=False)
        pats.append(tuple(sorted(sum(([int(v)] * k for v, k in zip(vals, sh)), []))))
    blocks = [np.array(orbit(p), dtype=np.int64) for p in pats]
    sizes = [len(b) for b in blocks]
    allD = np.concatenate(blocks)
    idx = np.repeat(np.arange(B), sizes)
    Z = (allD[:, None, :] * cube[None, :, :]).reshape(-1, m)
    def vec(fn):
        vals = (fn(Z).reshape(len(allD), len(cube)) * sign).sum(axis=1)
        out = np.zeros(B, dtype=object)
        # exact integer accumulation
        acc = np.zeros(B, dtype=np.int64)
        np.add.at(acc, idx, vals % P)
        return acc % P
    cols = [vec(lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam]
    rows.append(np.array(cols).T); brow.append(vec(lambda Z: Z.max(axis=1)))
    A = np.concatenate(rows); b = np.concatenate(brow)
    r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b[:, None]], 1))
    print(f'batch {bt+1}: {A.shape[0]} tests, {len(fam)} germs: rank {r1}, with max {r2} ->',
          'SEPARATED' if r2 > r1 else 'not separated', f'({time.time()-t0:.0f}s)', flush=True)
    if r2 > r1:
        break
