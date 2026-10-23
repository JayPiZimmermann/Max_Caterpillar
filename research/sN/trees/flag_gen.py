#!/usr/bin/env python3
"""General flag invariants (research/sN/trees): flags are sequences of m-2 vectors u from a pool
(subset indicators 1_X), recursion tau(G) = tau(argmax_u G) - tau(argmin_u G) in the quotient,
final stage: lattice length of the remaining segment measured by a functional w independent of the u's.
Tests whether max_m is separated from a germ family by some combination of these invariants.
Usage: flag_gen.py m R mode [pool]   pool in {sub (all 1_X), coord (only e_i)}"""
import sys, itertools
import numpy as np
from fractions import Fraction
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import forests, is_ham_path, is_spanning, heads, rank_mod_p
from flag_test import pyramid

def indep(vecs, m):
    M = np.array(list(vecs) + [[1] * m], dtype=float)
    return np.linalg.matrix_rank(M) == len(M)

def make_flags(m, pool):
    flags = []
    for seq in itertools.permutations(range(len(pool)), m - 2):
        U = [pool[i] for i in seq]
        if not indep(U, m):
            continue
        # final functional w: a vector independent of U and 1
        for w in itertools.chain(([1 if k == j else 0 for k in range(m)] for j in range(m)),):
            if indep(U + [w], m):
                break
        flags.append((U, w))
    return flags

def dot(p, u):
    return sum(x * y for x, y in zip(p, u))

def tau(G, U, w):
    if not U:
        vals = [dot(p, w) for p in G]
        return max(vals) - min(vals)
    u = U[0]
    vals = [dot(p, u) for p in G]
    lo, hi = min(vals), max(vals)
    return tau([p for p in G if dot(p, u) == hi], U[1:], w) - tau([p for p in G if dot(p, u) == lo], U[1:], w)

def main():
    m, R, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    poolname = sys.argv[4] if len(sys.argv) > 4 else 'sub'
    if poolname == 'sub':
        pool = []
        for r in range(1, m):
            for X in itertools.combinations(range(m), r):
                if 0 in X:  # 1_X ~ -1_{X^c}: keep one representative
                    pool.append([1 if k in X else 0 for k in range(m)])
    else:
        pool = [[1 if k == j else 0 for k in range(m)] for j in range(m)]
    flags = make_flags(m, pool)
    rest = list(range(1, m))
    Fs = [F for F in forests(rest) if is_spanning(F, rest)]
    sel = {'top': lambda F: True, 'nopath': lambda F: not is_ham_path(F, rest),
           'nostar': lambda F: max(sum(1 for e in F if v in e) for v in rest) < len(rest) - 1}[mode]
    Fs = [F for F in Fs if sel(F)]
    cols = []
    for ap in range(m):
        perm = list(range(m)); perm[0], perm[ap] = perm[ap], perm[0]
        for F in Fs:
            FF = [(perm[i], perm[j]) for i, j in F]
            for v in heads(m, 0, R):
                vv = [0] * m
                for t in range(m):
                    vv[perm[t]] = v[t]
                G = pyramid(m, vv, FF)
                cols.append([tau(G, U, w) for U, w in flags])
    simplex = [tuple(1 if k == j else 0 for k in range(m)) for j in range(m)]
    b = [tau(simplex, U, w) for U, w in flags]
    A = np.array(cols, dtype=np.int64).T
    r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, np.array(b, dtype=np.int64)[:, None]], axis=1))
    print(f'm={m} R={R} mode={mode} pool={poolname}: {len(cols)} top germs, {len(flags)} flags, '
          f'max nonzero on {sum(1 for x in b if x)} flags; rank {r1}, with max {r2} -> '
          f'{"SEPARATED" if r2 > r1 else "not separated"}', flush=True)

if __name__ == '__main__':
    main()
