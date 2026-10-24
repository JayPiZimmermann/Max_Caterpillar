"""V_loc(rays) vs V inside W, orbit-classified.  usage: run_rays2.py N [prime]"""
import random, sys, time, json
import numpy as np
from germs2 import Setup, rays, canon, rref, PR, rank_big

N = int(sys.argv[1]); p = int(sys.argv[2]) if len(sys.argv) > 2 else PR
t0 = time.time()
S = Setup(N, p)
dimV = rank_big(S.Vmat, p)
print('dimW', S.dimW, 'dimV', dimV, 'codim', S.dimW - dimV, f'{time.time()-t0:.1f}s', flush=True)
R = rays(N, S.H + S.braid)
classes = {}
for x in R:
    classes.setdefault(canon(x), []).append(x)
print('rays', len(R), 'classes', len(classes), f'{time.time()-t0:.1f}s', flush=True)
rng = random.Random(1)
deficit = {}
for c, xs in classes.items():
    _, rW, rV = S.local_conditions(xs[0], rng)
    if rW > rV:
        deficit[c] = (rW, rV)
print('classes with local conditions:', len(deficit), f'{time.time()-t0:.1f}s', flush=True)
for c, d in sorted(deficit.items()):
    print('  ', c, 'germ dims W,V =', d, 'orbit', len(classes[c]))
acc = np.zeros((0, S.dimW), dtype=np.int64)
for c in deficit:
    for x in classes[c]:
        Rr, rW, rV = S.local_conditions(x, rng)
        acc = np.concatenate([acc, Rr])
    acc, _ = rref(acc, p)
    print('  after class', c, 'rank', acc.shape[0], flush=True)
print('dim V_loc(rays) =', S.dimW - acc.shape[0], ' dim V =', dimV, f'{time.time()-t0:.1f}s')
