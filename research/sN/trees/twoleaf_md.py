#!/usr/bin/env python3
"""Can mixed differences kill every germ having a vertex c with >= 2 out-leaves (leaf l of F
attached to c, term relu(z_l - z_c), head entry v_l = 0), but not max_m?
Germs: G(a,v,F) = relu(<v,z> + sum_{(i,j) in F oriented} relu(z_i - z_j)), apex a (v_a = -1),
F any forest on T\\{a} with explicit orientations, heads |v_t| <= R, sum v = 0.
Features: m-th mixed differences over boxes (base q, step vector d), q near 0.
Usage: twoleaf_md.py m R ntests seed"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import forests, heads, rank_mod_p

def two_outleaves(v, F):
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    cnt = {}
    for (i, j) in F:            # oriented: term relu(z_i - z_j)
        if deg[i] == 1 and v[i] == 0:      # leaf i, centre j, relu(z_i - z_j)
            cnt[j] = cnt.get(j, 0) + 1
    return any(x >= 2 for x in cnt.values())

def main():
    m, R, nt, seed = map(int, sys.argv[1:5])
    rest = list(range(1, m))
    fams = []
    for F in forests(rest):
        for ori in itertools.product([0, 1], repeat=len(F)):
            FF = tuple((i, j) if o == 0 else (j, i) for (i, j), o in zip(F, ori))
            for v in heads(m, 0, R):
                if two_outleaves(v, FF):
                    fams.append((v, FF))
    # all apices by symmetry: max_m symmetric, but the MD features are not symmetrised -> add apex perms
    allf = []
    for ap in range(m):
        perm = list(range(m)); perm[0], perm[ap] = perm[ap], perm[0]
        for v, FF in fams:
            vv = [0] * m
            for t in range(m): vv[perm[t]] = v[t]
            allf.append((tuple(vv), tuple((perm[i], perm[j]) for i, j in FF)))
    allf = list(set(allf))
    random.seed(seed)
    subsets = list(itertools.product([0, 1], repeat=m))
    def ev(f, z):
        if f == 'max': return max(z)
        v, FF = f
        s = sum(a * b for a, b in zip(v, z)) + sum(max(0, z[i] - z[j]) for i, j in FF)
        return max(0, s)
    tests = []
    for _ in range(nt):
        d = [random.randint(1, 50) for _ in range(m)]
        q = [0] * m if random.random() < 0.5 else [random.randint(-60, 60) for _ in range(m)]
        tests.append((q, d))
    def md(f, q, d):
        return sum((-1) ** (m - sum(S)) * ev(f, [q[i] + d[i] * S[i] for i in range(m)]) for S in subsets)
    A = np.array([[md(f, q, d) for f in allf] for q, d in tests], dtype=np.int64)
    b = np.array([[md('max', q, d)] for q, d in tests], dtype=np.int64)
    r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, b], axis=1))
    print(f'm={m} R={R}: {len(allf)} germs with >=2 out-leaves at one centre; {nt} MD tests; rank {r1}, with max {r2} -> {"SEPARATED" if r2 > r1 else "not separated"}', flush=True)

if __name__ == '__main__':
    main()
