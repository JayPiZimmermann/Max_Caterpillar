"""V_loc(rays) versus V inside W.  usage: run_rays.py N"""
import random, sys, time
import flint
from germs import Setup, rays

def stack_rank(blocks, ncols, p):
    n = sum(b.nrows() for b in blocks)
    M = flint.nmod_mat(n, ncols, p)
    r = 0
    for b in blocks:
        for i in range(b.nrows()):
            for j in range(ncols):
                M[r, j] = b[i, j]
            r += 1
    return M.rank()

N = int(sys.argv[1])
t0 = time.time()
S = Setup(N)
print('dimW', S.dimW, 'dimV', S.dimV, 'codim', S.dimW - S.dimV, f'{time.time()-t0:.1f}s', flush=True)
R = rays(N, S.H + S.braid)
print('rays', len(R), flush=True)
rng = random.Random(1)
blocks, stats = [], {}
for k, x0 in enumerate(R):
    G, rW, rV = S.local_conditions(x0, rng)
    if G.nrows():
        blocks.append(G)
    stats[(rW, rV)] = stats.get((rW, rV), 0) + 1
print('germ dims (W,V): count', sorted(stats.items()))
r = stack_rank(blocks, S.dimW, S.p)
print('rank of all ray conditions', r, ' dim V_loc(rays) =', S.dimW - r, ' dim V =', S.dimV, f'{time.time()-t0:.1f}s')
