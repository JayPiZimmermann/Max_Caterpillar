"""Structural superset S_4 of 4-locality germs (any N):
apex a in T with v_a = -1 and no hinge at a; on R = T - {a}: v_t >= -1, sum_T v = 0
(so v_t <= 3), hinges M = an oriented forest on R (relu(z_p - z_c)).
Germ g(z) = relu(<v,z> + sum_{(p,c) in M} relu(z_p - z_c)).
Check: every pair (and singleton) of FULL germs of S_4 is killed by some mixed 4th
difference D_{base,c} with D max_4 != 0.  Writes a greedy small stencil family.
usage: superset4.py B cvals"""
import sys, itertools, json
import numpy as np
B = int(sys.argv[1]); CV = [int(x) for x in sys.argv[2].split(',')]
m = 4
germs = set()
for a in range(m):
    R = [t for t in range(m) if t != a]
    for vr in itertools.product(range(-1, 4), repeat=3):
        if sum(vr) != 1: continue
        v = [0] * m; v[a] = -1
        for t, x in zip(R, vr): v[t] = x
        und = [(R[0], R[1]), (R[0], R[2]), (R[1], R[2])]
        for r in range(3):
            for E in itertools.combinations(und, r):
                for ori in itertools.product([0, 1], repeat=r):
                    M = tuple(sorted((e if o == 0 else (e[1], e[0])) for e, o in zip(E, ori)))
                    if all(v[t] != 0 or any(t in e for e in M) for t in range(m)):
                        germs.add((tuple(v), M))
germs = sorted(germs)
print('superset full germs (raw, unnormalized)', len(germs), flush=True)
lo, hi = -B, B + max(CV)
n1 = hi - lo + 1
rng = np.arange(lo, hi + 1)
grid = np.array(np.meshgrid(np.arange(0, max(CV) + 1), rng, rng, rng, indexing='ij')).reshape(m, -1).T
def idx(p):
    return p[..., 0] * n1 ** 3 + (p[..., 1] - lo) * n1 ** 2 + (p[..., 2] - lo) * n1 + (p[..., 3] - lo)
vals = np.zeros((len(germs), len(grid)), dtype=np.int64)
for k, (v, M) in enumerate(germs):
    a = grid @ np.array(v)
    for p, c in M:
        a = a + np.maximum(grid[:, p] - grid[:, c], 0)
    vals[k] = np.maximum(a, 0)
mx = grid.max(1)
funcs = []
for a in itertools.product(range(-B, B + 1), repeat=m - 1):
    base = (0,) + a
    for c in itertools.product(CV, repeat=m):
        pts, sg = [], []
        for S in range(1 << m):
            p = list(base)
            for i in range(m):
                if S >> i & 1: p[i] += c[i]
            pts.append(p); sg.append((-1) ** (m - bin(S).count('1')))
        ii = idx(np.array(pts)); sg = np.array(sg)
        dm = int((sg * mx[ii]).sum())
        if dm == 0: continue
        funcs.append((base, c, ii, sg, dm))
print('functionals', len(funcs), flush=True)
K = np.zeros((len(germs), len(funcs)), dtype=bool)
for f, (_, _, ii, sg, _) in enumerate(funcs):
    K[:, f] = (vals[:, ii] @ sg) == 0
n = len(germs)
uncovered = []
for g in range(n):
    ok = (K[g][None, :] & K[g:]).any(1)
    for h in np.nonzero(~ok)[0]:
        uncovered.append((g, g + h))
print('pairs/singletons not killed:', len(uncovered))
for g, h in uncovered[:15]:
    print('  ', germs[g], germs[h])
if not uncovered:
    # greedy family covering all pairs
    need = set((g, h) for g in range(n) for h in range(g, n))
    fam = []
    while need:
        best, bc = None, -1
        cnt = np.zeros(len(funcs), dtype=np.int64)
        # count covered pairs per functional: sum over needed pairs
        P = np.array(list(need))
        cnt = (K[P[:, 0]] & K[P[:, 1]]).sum(0)
        f = int(cnt.argmax())
        fam.append(f)
        covered = K[P[:, 0], f] & K[P[:, 1], f]
        need -= set(map(tuple, P[covered].tolist()))
        print('  pick', funcs[f][0], funcs[f][1], 'Dmax', funcs[f][4], 'covers', int(cnt[f]), 'left', len(need), flush=True)
    json.dump({'germs': [[list(v), [list(e) for e in M]] for v, M in germs],
               'stencils': [{'base': list(funcs[f][0]), 'steps': list(funcs[f][1]), 'Dmax': funcs[f][4]} for f in fam]},
              open('cert4.json', 'w'))
    print('family size', len(fam))
