"""Inspect the flats of flats2_N5.pkl with the largest recorded passing sets:
recompute each flat's neuron space exactly (Fractions) from its implied localities,
and re-test passing at random rational points (exact)."""
import pickle, itertools, random, sys
from fractions import Fraction as Fr
from passing import localities, passes
from flats2 import nullspace_q
N = 5
d = pickle.load(open('flats2_N5.pkl', 'rb'))
locs = d['locs']; flats = d['flats']
pr = list(itertools.combinations(range(N), 2)); idx = {p: i for i, p in enumerate(pr)}; nv = len(pr) + N
def rows_of(i):
    T, order = locs[i]; rows = []; above = list(T)
    for o in order:
        r = [0] * nv
        for j in above: r[idx[(min(o, j), max(o, j))]] += 1
        r[len(pr) + o] -= 1; rows.append(r); above.append(o)
    return rows
best = sorted(flats.values(), key=lambda v: -bin(v[2]).count('1'))
top = int(sys.argv[1]) if len(sys.argv) > 1 else 3
shown = set()
rnd = random.Random(5)
for rk, cl, pas in best:
    if pas in shown: continue
    shown.add(pas)
    if len(shown) > top: break
    rows = [[-1] * len(pr) + [1] * N]
    for i in range(len(locs)):
        if (cl >> i) & 1: rows += rows_of(i)
    B = nullspace_q(rows, nv)
    print('passing', bin(pas).count('1'), 'implied locs', bin(cl).count('1'), 'dim', len(B))
    print('  passed:', [(locs[i][0], locs[i][1]) for i in range(len(locs)) if (pas >> i) & 1])
    for b in B:
        print('  basis a:', {p: str(b[i]) for i, p in enumerate(pr) if b[i]}, 'kappa', [str(x) for x in b[len(pr):]])
    cnt = []
    for _ in range(5):
        cf = [rnd.randint(-30, 30) for _ in B]
        pt = [sum(c * b[j] for c, b in zip(cf, B)) for j in range(nv)]
        a = {p: pt[i] for i, p in enumerate(pr) if pt[i] != 0}
        cnt.append(sum(passes(a, pt[len(pr):], *L) for L in locs))
    print('  exact passing counts at 5 random points of the flat:', cnt)
