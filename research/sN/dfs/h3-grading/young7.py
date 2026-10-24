"""Graded rank of the S_mu-(twisted-)invariant part of A_N + span{U_k : |M_k| <= j}, for large N.
Same object as grade.py (columns = twisted S_mu-orbit sums of aux functions (all ordered pairs, +-x_i)
and keys; blocks: A, then keys by |M|), but evaluation streamed through ysev.c with the trivial
second group (no full key x point matrix in memory).  npts defaults to ncols + 40, so a rank
below npts is not limited by the number of points.  Mod-p ranks: lower bounds (measured).
Output line is compatible with grade.py logs (tabulate.py).
Usage: young7.py N mu twist [npts] [seed]"""
import sys, json, time, os, subprocess
import numpy as np
from common import keys, HERE
from sym import act_key, orbits, young_gens, run_rank
N = int(sys.argv[1]); mu = tuple(int(c) for c in sys.argv[2]); tw = sys.argv[3]
npts_arg = int(sys.argv[4]) if len(sys.argv) > 4 and int(sys.argv[4]) > 0 else None
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
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
orbs = [o for o, odd in orbits(fam, act_key, young_gens(N, mu)) if not (tw == 'sgn' and odd)]
fidx = {k: n for n, k in enumerate(fam)}
orbs.sort(key=lambda o: grade[fidx[next(iter(o))]])
ogr = [grade[fidx[next(iter(o))]] for o in orbs]
grades = sorted(set(ogr))
npts = npts_arg or len(orbs) + 40
rng = np.random.default_rng(seed)
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
tag = f'y7_{N}_{"".join(map(str, mu))}_{tw}_{seed}_{os.getpid()}'
fin = os.path.join(HERE, tag + '.in'); fout = os.path.join(HERE, tag + '.out')
buf = [N, len(fam)]
for h, M in fam:
    buf += list(h) + [len(M)]
    for i, j in sorted(M): buf += [i, j]
buf += [len(orbs)]
for o in orbs:
    buf += [len(o)]
    for k, sg in o.items(): buf += [fidx[k], sg if tw == 'sgn' else 1]
buf += [npts] + list(X.ravel()) + [1, 1] + list(range(N))
np.array(buf, dtype='<i8').tofile(fin)
del buf
t1 = time.time()
subprocess.run([os.path.join(HERE, 'ysev'), fin, fout], check=True)
Mat = np.fromfile(fout, dtype='<i8').reshape(len(orbs), npts)
os.remove(fin); os.remove(fout)
t2 = time.time()
blocks = [Mat[[c for c in range(len(orbs)) if ogr[c] == gr]] for gr in grades]
del Mat
r = run_rank(blocks, tag)
print(json.dumps({'N': N, 'mu': mu, 'twist': tw, 'seed': seed, 'npts': npts, 'grades': grades,
                  'ncols': [b.shape[0] for b in blocks], 'ranks_A_then_by_M': r, 'saturated': r[-1] >= npts,
                  'secs': [round(t1 - t0, 1), round(t2 - t1, 1), round(time.time() - t2, 1)]}), flush=True)
