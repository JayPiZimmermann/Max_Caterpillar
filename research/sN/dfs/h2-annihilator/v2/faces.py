"""Enumerate codim-2 faces (one interior point each) of the global fan for N,
classified up to S_N (translation normalised).  Saves faces_N.pkl:
{canon: [points]}.  usage: faces.py N"""
import itertools, math, pickle, sys, time
import numpy as np
sys.path.insert(0, '..')
from germs2 import rays, canon
from hyperplanes import global_hyperplanes

N = int(sys.argv[1])
t0 = time.time()
H, Bd = global_hyperplanes(N)
hyps = H + Bd
Hs = np.array(hyps, dtype=np.int64)
R = np.array(rays(N, hyps), dtype=np.int64)
Z = (R @ Hs.T == 0)
print('hyps', len(hyps), 'rays', len(R), f'{time.time()-t0:.1f}s', flush=True)
flats = {}
for a, b in itertools.combinations(range(len(Hs)), 2):
    if np.linalg.matrix_rank(Hs[[a, b]]) < 2:
        continue
    inside = tuple(np.flatnonzero(Z[:, a] & Z[:, b]))
    flats.setdefault(inside, (a, b))
print('codim-2 flats', len(flats), flush=True)
# a codim-2 flat has dimension N-3 in R^N/R1.  Faces = chambers of the
# arrangement induced on the flat.  For N-3 = 1 (N=4) a flat is a line: 2 faces
# (its two rays).  For N-3 = 2 (N=5): consecutive ray sectors.  For general N we
# sample: interior points of faces = sums of ray subsets that are generic; we
# instead take random positive combinations of rays in the flat and dedupe by
# sign vector.
points = {}
for key, (a, b) in flats.items():
    rs = R[list(key)]
    if N == 4:
        cand = [r for r in rs]
    elif N == 5:
        r0 = rs[0]
        r1 = next(r for r in rs if np.linalg.matrix_rank(np.stack([r0, r])) == 2)
        Bm = np.stack([r0, r1]).T.astype(float)
        ang = []
        for r in rs:
            c, *_ = np.linalg.lstsq(Bm, r.astype(float), rcond=None)
            ang.append(math.atan2(c[1], c[0]))
        order = [rs[i] for i in np.argsort(ang)]
        cand = [order[i] + order[(i + 1) % len(order)] for i in range(len(order))]
    else:
        raise NotImplementedError
    for q in cand:
        if not q.any():
            continue
        g = np.gcd.reduce(np.abs(q))
        q = tuple(int(v) for v in q // g)
        sv = tuple(np.sign(Hs @ np.array(q)))
        if sum(1 for s in sv if s == 0) and np.linalg.matrix_rank(Hs[[i for i, s in enumerate(sv) if s == 0]]) == 2:
            points[sv] = q
print('codim-2 faces', len(points), f'{time.time()-t0:.1f}s', flush=True)
classes = {}
for q in points.values():
    classes.setdefault(canon(q), []).append(q)
print('classes', len(classes), f'{time.time()-t0:.1f}s', flush=True)
pickle.dump(classes, open(f'faces_{N}.pkl', 'wb'))
