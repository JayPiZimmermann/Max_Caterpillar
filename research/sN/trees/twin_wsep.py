#!/usr/bin/env python3
"""Separation test in the unit-cube formulation with anchors of bounded spread.
Phi_W f = sum_{orbits O of normalised anchors (min 0, entries <= k)} W_O sum_{y in O} U_y f.
Usage: twin_wsep.py m R k [family: twin|two] [sparse]"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import eval_germ, orbit, rank_mod_p, left_kernel_frac
from twin_wbar import anchors, ufeat
import sym_md
m, R, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
famname = sys.argv[4] if len(sys.argv) > 4 else 'twin'
def twin_small(v, F, B=1):
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    sig = {}
    for (i, j) in F:
        if deg[i] == 1 and abs(v[i]) <= B: key = (j, 'o', v[i]); sig[key] = sig.get(key, 0) + 1
        if deg[j] == 1 and abs(v[j]) <= B: key = (i, 'i', v[j]); sig[key] = sig.get(key, 0) + 1
    return any(x >= 2 for x in sig.values())
sym_md.MODE['pred'] = {'twin': sym_md.twin_leaves, 'two': sym_md.two_outleaves, 'twin1': twin_small}[famname]
t0 = time.time()
fam = sym_md.family(m, R)
reps = anchors(m, k)
A = np.array([ufeat(m, reps, lambda Z, v=v, F=F: eval_germ(v, F, Z)) for v, F in fam]).T
bm = np.array(ufeat(m, reps, lambda Z: Z.max(axis=1)))
r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, bm[:, None]], 1))
print(f'm={m} R={R} k={k} {famname}: {len(fam)} germs, {len(reps)} anchor orbits, rank {r1}, with max {r2} ->',
      'SEPARATED' if r2 > r1 else 'not separated', f'({time.time()-t0:.0f}s)', flush=True)
if len(sys.argv) > 5 and r2 > r1:
    np.save(f'/tmp/claude-1342076897/-home-jzimmermann-code-Max-Caterpillar/959f7190-775e-44f9-8707-e5e072ae6f20/scratchpad/A_{m}_{R}_{k}_{famname}.npy', A)
