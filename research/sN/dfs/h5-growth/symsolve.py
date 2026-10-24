"""Symmetric ansatz for caterpillar expansions of max_N (upper bounds on s_N).

For a permutation group H (generators on the command line), an H-invariant
expansion has one coefficient per H-orbit of units.  Rows (kink groups,
Moebius rows) are aggregated over orbits.  We find, mod p, the affine solution
space in orbit coordinates and greedily zero orbits (largest first) while the
system stays solvable; the result is re-solved exactly over Q on the remaining
orbits and written as a support (expanded to units) with exact coefficients.
usage: python symsolve.py N mode gens seed out.pkl   (mode full|top; gens "1,0,2,3,4;...")
"""
import pickle
import sys
import time
from fractions import Fraction

import flint
import numpy as np

from kf import build

P = 2147483629
N, MODE, GENS, SEED, OUT = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
rng = np.random.default_rng(SEED)
t0 = time.time()
U, groups, Dm, tD = build(N)
n = len(U)
print('loaded', n, 'units', len(groups), 'groups', f'{time.time()-t0:.0f}s', flush=True)
idx = {k: i for i, k in enumerate(U)}
gens = [tuple(int(t) for t in g.split(',')) for g in GENS.split(';')] if GENS else []


def norm(h, pairs):
    h = list(h); M = []
    for a, b in pairs:
        if a > b:
            h[a] += 1; h[b] -= 1; a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))


def pk(key, p):
    h, M = key
    h2 = [0] * N
    for i in range(N):
        h2[p[i]] = h[i]
    return norm(h2, [(p[a], p[b]) for a, b in M])


orb = [-1] * n
orbits = []
for u in range(n):
    if orb[u] >= 0:
        continue
    o = [u]; orb[u] = len(orbits); st = [u]
    while st:
        v = st.pop()
        for g in gens:
            w = idx[pk(U[v], g)]
            if orb[w] < 0:
                orb[w] = len(orbits); o.append(w); st.append(w)
    orbits.append(o)
no = len(orbits)
print('orbits', no, flush=True)
rows = {}
for g in groups.values():
    acc = {}
    for u, lam in g.items():
        acc[orb[u]] = acc.get(orb[u], 0) + lam
    acc = tuple(sorted((o, v) for o, v in acc.items() if v))
    if acc:
        rows[acc] = 0
rows = [(dict(a), 0) for a in rows]
SR = [Dm.shape[0] - 1] if MODE == 'top' else range(Dm.shape[0])
for s in SR:
    acc = {}
    for u in np.nonzero(Dm[s])[0]:
        acc[orb[u]] = acc.get(orb[u], 0) + int(Dm[s, u])
    rows.append(({o: v for o, v in acc.items() if v}, int(tD[s])))
print('aggregated rows', len(rows), flush=True)


def matrix(cols):
    pos = {o: i for i, o in enumerate(cols)}
    out = []
    for a, b in rows:
        r = [0] * (len(cols) + 1)
        nzr = False
        for o, v in a.items():
            if o in pos:
                r[pos[o]] = v; nzr = True
        r[-1] = b
        if nzr or b:
            out.append(r)
    return out


def consistent_modp(cols):
    A = matrix(cols)
    m = len(cols)
    if not A:
        return True
    M1 = flint.nmod_mat([[x % P for x in r[:m]] for r in A], P) if m else None
    M2 = flint.nmod_mat([[x % P for x in r] for r in A], P)
    r1 = M1.rank() if m else 0
    return r1 == M2.rank()


cols = list(range(no))
assert consistent_modp(cols), 'symmetric system infeasible'
# greedy: try to drop orbits, largest orbit first (random tie-break)
order = sorted(cols, key=lambda o: (-len(orbits[o]), rng.random()))
for o in order:
    c2 = [c for c in cols if c != o]
    if c2 and consistent_modp(c2):
        cols = c2
print('kept orbits', len(cols), 'support', sum(len(orbits[o]) for o in cols), f'{time.time()-t0:.0f}s', flush=True)
A = matrix(cols)
M = flint.fmpq_mat(len(A), len(cols) + 1, [x for r in A for x in r])
R, rk = M.rref()
sol = {}
m = len(cols)
for i in range(rk):
    j = next(j for j in range(m + 1) if R[i, j] != 0)
    assert j < m, 'inconsistent over Q'
    sol[cols[j]] = Fraction(int(R[i, m].p), int(R[i, m].q))
d = {}
for o, v in sol.items():
    if v != 0:
        for u in orbits[o]:
            d[U[u]] = v
print('exact support', len(d), flush=True)
pickle.dump({'N': N, 'mode': MODE, 'gens': GENS, 'K': sorted(d), 'd': d}, open(OUT, 'wb'))
