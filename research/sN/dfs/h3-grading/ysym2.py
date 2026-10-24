"""m_lam(V_N) and graded prefixes via a primitive idempotent of type lam (Young symmetrizer).
Group G1 in {row group R, column group C} acts on the family (columns = G1-orbit sums, signed
if G1 = C); the other group G2 is summed over at the evaluation points (signed if G2 = C).
dim(e V) = m_lam for e = a_T b_T or b_T a_T.  Mod-p ranks: lower bounds, measured.
Usage: ysym2.py N lam npts [seed] [g2=auto|R|C]"""
import sys, json, time, itertools, os, struct, subprocess
import numpy as np
from common import keys, HERE
from sym import act_key, orbits, run_rank
N = int(sys.argv[1]); lam = tuple(int(c) for c in sys.argv[2]); npts = int(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1; which = sys.argv[5] if len(sys.argv) > 5 else 'auto'
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
def group_elems(blocks, signed):
    out = []
    for perms in itertools.product(*[itertools.permutations(b) for b in blocks]):
        g = list(range(N))
        for b, pb in zip(blocks, perms):
            for a, c in zip(b, pb): g[a] = c
        sg = 1
        if signed:   # sign of permutation g
            seen = [False] * N
            for i in range(N):
                if not seen[i]:
                    j, L = i, 0
                    while not seen[j]: seen[j] = True; j = g[j]; L += 1
                    if L % 2 == 0: sg = -sg
        out.append((sg, g))
    return out
import math
sizeR = math.prod(math.factorial(l) for l in lam); sizeC = math.prod(math.factorial(len(c)) for c in cols)
g2 = which if which != 'auto' else ('C' if sizeC <= sizeR else 'R')
if g2 == 'C':
    G1gens = [transp(r[0], r[t]) for r in rows for t in range(1, len(r))]; tw1 = False
    G2 = group_elems(cols, True)
else:
    G1gens = [transp(c[0], c[t]) for c in cols for t in range(1, len(c))]; tw1 = True
    G2 = group_elems(rows, False)
orbs = [o for o, odd in orbits(fam, act_key, G1gens) if not (tw1 and odd)]
fidx = {k: n for n, k in enumerate(fam)}
orbs.sort(key=lambda o: grade[fidx[next(iter(o))]])
ogr = [grade[fidx[next(iter(o))]] for o in orbs]
grades = sorted(set(ogr))
rng = np.random.default_rng(seed)
X = rng.integers(-10**6, 10**6, size=(npts, N), endpoint=True).astype(np.int64)
tag = f'ys2_{N}_{"".join(map(str, lam))}_{seed}_{os.getpid()}'
fin = os.path.join(HERE, tag + '.in'); fout = os.path.join(HERE, tag + '.out')
buf = [N, len(fam)]
for h, M in fam:
    buf += list(h) + [len(M)]
    for i, j in sorted(M): buf += [i, j]
buf += [len(orbs)]
for o in orbs:
    buf += [len(o)]
    for k, sg in o.items(): buf += [fidx[k], sg if tw1 else 1]
buf += [npts] + list(X.ravel()) + [len(G2)]
for sg, g in G2: buf += [sg] + list(g)
np.array(buf, dtype='<i8').tofile(fin)
t1 = time.time()
subprocess.run([os.path.join(HERE, 'ysev'), fin, fout], check=True)
Mat = np.fromfile(fout, dtype='<i8').reshape(len(orbs), npts)
os.remove(fin); os.remove(fout)
t2 = time.time()
blocks = [Mat[[c for c in range(len(orbs)) if ogr[c] == gr]] for gr in grades]
r = run_rank(blocks, tag)
print(json.dumps({'N': N, 'lam': lam, 'G2': g2, '|G2|': len(G2), 'grades': grades, 'ncols': len(orbs), 'npts': npts,
                  'mult_prefix': r, 'saturated': r[-1] >= npts, 'secs': [round(t1 - t0, 1), round(t2 - t1, 1), round(time.time() - t2, 1)]}), flush=True)
