"""V_loc(codim-2 faces) versus V inside W.  usage: codim2.py N [prime]

Codim-2 faces of the global fan (braid + kink hyperplanes) on R^N/R1: every
2-dim flat P = H1 ∩ H2 ∩ ... is subdivided by the rays lying in it; for N >= 5
the codim-2 faces are (N-3)-dimensional... we use: N = 5 -> flats of dim 2,
interior points of consecutive-ray sectors.  For general N we take the
codim-2 flats as intersections of two hyperplanes and sample their faces by
random points (see sample_faces).
"""
import itertools
import math
import pickle
import random
import sys
import time

import numpy as np

from germs2 import Setup, rays, canon, rref, PR, rank_big


def flats2(hyps):
    Hs = np.array(hyps, dtype=np.int64)
    seen = {}
    for a, b in itertools.combinations(range(len(Hs)), 2):
        M = Hs[[a, b]]
        if np.linalg.matrix_rank(M) < 2:
            continue
        # the flat = all hyperplanes containing it; key = closure
        # compute nullspace basis (float ok for key via containment test)
        seen.setdefault((a, b), None)
    return seen


def main():
    N = int(sys.argv[1])
    p = int(sys.argv[2]) if len(sys.argv) > 2 else PR
    t0 = time.time()
    S = Setup(N, p)
    dimV = rank_big(S.Vmat, p)
    print('dimW', S.dimW, 'dimV', dimV, f'{time.time()-t0:.1f}s', flush=True)
    hyps = S.H + S.braid
    Hs = np.array(hyps, dtype=np.int64)
    R = np.array(rays(N, hyps), dtype=np.int64)
    Z = (R @ Hs.T == 0)               # ray x hyperplane incidence
    print('rays', len(R), flush=True)
    flats = {}
    for a, b in itertools.combinations(range(len(Hs)), 2):
        if np.linalg.matrix_rank(Hs[[a, b]]) < 2:
            continue
        inside = np.flatnonzero(Z[:, a] & Z[:, b])
        key = tuple(inside)
        if key in flats:
            continue
        flats[key] = (a, b)
    print('codim-2 flats (by ray content)', len(flats), flush=True)
    points = set()
    for key, (a, b) in flats.items():
        rs = R[list(key)]
        if N == 5:
            # 2-dim flat: cyclic order of rays
            r0 = rs[0]
            r1 = next(r for r in rs if np.linalg.matrix_rank(np.stack([r0, r])) == 2)
            Bm = np.stack([r0, r1]).T.astype(float)
            ang = []
            for r in rs:
                c, *_ = np.linalg.lstsq(Bm, r.astype(float), rcond=None)
                ang.append(math.atan2(c[1], c[0]))
            order = [rs[i] for i in np.argsort(ang)]
            for i in range(len(order)):
                q = order[i] + order[(i + 1) % len(order)]
                if q.any():
                    g = np.gcd.reduce(np.abs(q))
                    points.add(tuple(int(v) for v in q // g))
        else:
            raise NotImplementedError
    print('codim-2 face points', len(points), f'{time.time()-t0:.1f}s', flush=True)
    classes = {}
    for x in points:
        classes.setdefault(canon(x), []).append(x)
    print('classes', len(classes), f'{time.time()-t0:.1f}s', flush=True)
    rng = random.Random(2)
    deficit = {}
    for c, xs in classes.items():
        _, rW, rV = S.local_conditions(xs[0], rng)
        if rW > rV:
            deficit[c] = (rW, rV)
    print('classes with local conditions:', len(deficit), f'{time.time()-t0:.1f}s', flush=True)
    for c, d in sorted(deficit.items()):
        on = [hyps[i] for i in range(len(hyps)) if sum(u * v for u, v in zip(hyps[i], c)) == 0]
        print('  ', c, 'germ dims W,V =', d, 'orbit', len(classes[c]), 'hyps', on, flush=True)
    acc = np.zeros((0, S.dimW), dtype=np.int64)
    for c in deficit:
        for x in classes[c]:
            Rr, rW, rV = S.local_conditions(x, rng)
            acc = np.concatenate([acc, Rr])
        acc, _ = rref(acc, p)
        print('  after class', c, 'rank', acc.shape[0], flush=True)
    print('dim V_loc(codim2) =', S.dimW - acc.shape[0], ' dim V =', dimV, f'{time.time()-t0:.1f}s', flush=True)


if __name__ == '__main__':
    main()
