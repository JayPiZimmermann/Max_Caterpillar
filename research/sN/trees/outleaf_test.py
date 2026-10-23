#!/usr/bin/env python3
"""Germ-level test against out-star germs (research/sN/trees).
Germ G(a,v,F) as in pn_test.py (normalized pairs (i,j), i<j, term relu(z_i - z_j)).
A leaf l of F with neighbour c is an OUT-LEAF if, written as relu(z_l - z_c), its head entry is 0:
pair (l,c): v_l = 0;  pair (c,l): v_l = 1.
Question: is max_m in span{germs with an out-leaf} + span{germs with non-spanning F} + aux + lin?
Usage: outleaf_test.py m R"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import forests, is_spanning, heads, rank_mod_p

def has_outleaf(v, F):
    deg = {}
    for i, j in F:
        deg[i] = deg.get(i, 0) + 1; deg[j] = deg.get(j, 0) + 1
    for i, j in F:
        if deg[i] == 1 and v[i] == 0: return True   # leaf i, pair (i,j)
        if deg[j] == 1 and v[j] == 1: return True   # leaf j, pair (i,j) = (c,l)
    return False

def main():
    m, R = int(sys.argv[1]), int(sys.argv[2])
    rest = list(range(1, m)); Fs = forests(rest)
    perms = list(itertools.permutations(rest)); seen = set(); fams = []
    for F in Fs:
        for v in heads(m, 0, R):
            if is_spanning(F, rest) and not has_outleaf(v, F):
                continue
            best = None
            for p in perms:
                mp = {0: 0}; mp.update(dict(zip(rest, p)))
                vv = [0] * m
                for t in range(m): vv[mp[t]] = v[t]
                FF = tuple(sorted(tuple(sorted((mp[u], mp[w]))) for u, w in F))
                key = (tuple(vv), FF)
                if best is None or key < best: best = key
            # note: canonical form may change pair orientation; recheck out-leaf on canonical
            if best not in seen: seen.add(best); fams.append(best)
    fams = [f for f in fams if (not is_spanning(list(f[1]), rest)) or has_outleaf(f[0], f[1])]
    allp = list(itertools.permutations(range(m)))
    rng = np.random.default_rng(1)
    npts = len(fams) + 60
    X = rng.integers(-10**4, 10**4, size=(npts, m))
    cols = []
    for (v, F) in fams:
        v = np.array(v); tot = np.zeros(npts, dtype=np.int64)
        for p in allp:
            Z = X[:, p]; s = Z @ v
            for (i, j) in F: s = s + np.maximum(Z[:, i] - Z[:, j], 0)
            tot += np.maximum(s, 0)
        cols.append(tot)
    aux = sum(np.maximum(X[:, i] - X[:, j], 0) for i in range(m) for j in range(m) if i != j)
    B = np.stack(cols + [aux, X.sum(axis=1)], axis=1)
    r1 = rank_mod_p(B); r2 = rank_mod_p(np.concatenate([B, X.max(axis=1)[:, None]], axis=1))
    print(f'm={m} R={R}: {len(fams)} germ types (out-leaf or lower-dim); rank {r1}, with max {r2} -> max {"NOT in" if r2 > r1 else "IN"} span', flush=True)

if __name__ == '__main__':
    main()
