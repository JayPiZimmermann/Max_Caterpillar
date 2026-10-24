#!/usr/bin/env python3
"""Per-unit stratum data for the generalized locality method (weights/strata.py).

A locality is a stratum of the braid arrangement: an ordered set partition
(T = B_1 > B_2 > ... > B_m) of the N coordinates with |T| >= 3, taken at a
generic point p of the stratum.  (Points on a stratum that are not generic,
and the hyperplanes x_i = 0, give dominated localities: see README.md.)

For a unit U_{h,M} and generic p on the stratum, U_k is nonzero modulo the
auxiliary germs only if A_k vanishes identically on the stratum, i.e. every
block coefficient vanishes:

    c_b = sum_{o in b} kappa_o - |M(b)| - e_M(b, above b) = 0     for every b,

kappa_o = h_o + #{j : (o, j) in M}.  The germ restricted to moves of the top
block T is then the T-germ

    g(z_T) = relu(<v_T, z_T> + sum_{(i,j) in M(T)} relu(z_i - z_j)),
    v_t = kappa_t - #{j in T : (t, j) in M},

which depends on T only (not on the lower blocks).

For every canonical unit (identity-labelled caterpillar, all face states,
auxiliary descriptions removed) and every top set T this script records the
T-germ (v_T, M(T)) in positional coordinates of sorted(T), and for every
lower composition c' (block sizes from top to bottom) the number n(k, T, c')
of ordered set partitions of the other coordinates of type c' satisfying all
block conditions.  Exact integer counts (DP over placed subsets).

Usage: python3 strata.py N [workers]     -> data/strata_N.pkl
"""
import itertools
import os
import pickle
import sys
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'scripts'))
import vocabulary_search as vs

HERE = os.path.dirname(os.path.abspath(__file__))


def canonical_units(N):
    ident = tuple(range(N))
    out = set()
    r = N - 2
    for size in range(1, r + 1):
        for S in itertools.combinations(range(1, r + 1), size):
            out |= vs.normalized_faces(N, ident, frozenset(S))
    return sorted((k for k in out if not vs.is_auxiliary(k)),
                  key=lambda k: (k[0], sorted(k[1])))


def unit_data(args):
    N, key = args
    h, M = key
    kappa = list(h)
    for i, j in M:
        kappa[i] += 1
    res = {}
    for t in range(3, N + 1):
        for T in itertools.combinations(range(N), t):
            Ts = set(T)
            pos = {x: a for a, x in enumerate(T)}
            vT = tuple(kappa[x] - sum(1 for (i, j) in M if i == x and j in Ts) for x in T)
            MT = frozenset((pos[i], pos[j]) for (i, j) in M if i in Ts and j in Ts)
            rest = [o for o in range(N) if o not in Ts]
            n = len(rest)
            idx = {o: a for a, o in enumerate(rest)}
            adj = [0] * n            # M-neighbours inside rest, as bitmask
            eT = [0] * n             # number of M-neighbours in T
            for i, j in M:
                if i in idx and j in idx:
                    adj[idx[i]] |= 1 << idx[j]
                    adj[idx[j]] |= 1 << idx[i]
                elif i in idx and j in Ts:
                    eT[idx[i]] += 1
                elif j in idx and i in Ts:
                    eT[idx[j]] += 1
            full = (1 << n) - 1
            base = {}                # mask b -> sum kappa - |M(b)| - e(b, T)
            for b in range(1, full + 1):
                s = 0
                inner = 0
                for a in range(n):
                    if b >> a & 1:
                        s += kappa[rest[a]] - eT[a]
                        inner += bin(adj[a] & b).count('1')
                base[b] = s - inner // 2
            dp = {(0, ()): 1}
            final = {}
            frontier = dp
            while frontier:
                new = {}
                for (placed, comp), c in frontier.items():
                    free = full & ~placed
                    b = free
                    while b:
                        e = 0
                        bb = b
                        while bb:
                            low = bb & -bb
                            a = low.bit_length() - 1
                            e += bin(adj[a] & placed).count('1')
                            bb ^= low
                        if base[b] - e == 0:
                            st = (placed | b, comp + (bin(b).count('1'),))
                            if placed | b == full:
                                final[st[1]] = final.get(st[1], 0) + c
                            else:
                                new[st] = new.get(st, 0) + c
                        b = (b - 1) & free
                frontier = new
            if n == 0:
                final = {(): 1}
            if final:
                res[T] = ((vT, MT), final)
    return key, res


def main():
    N = int(sys.argv[1])
    W = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    units = canonical_units(N)
    print('N', N, 'canonical units', len(units), flush=True)
    with Pool(W) as pool:
        data = pool.map(unit_data, [(N, k) for k in units], chunksize=16)
    os.makedirs(os.path.join(HERE, 'data'), exist_ok=True)
    with open(os.path.join(HERE, 'data', f'strata_{N}.pkl'), 'wb') as f:
        pickle.dump((N, data), f)
    germs = set()
    for _, res in data:
        for T, (g, _) in res.items():
            germs.add((len(T), g))
    from collections import Counter
    print('distinct T-germs by |T|:', dict(Counter(n for n, _ in germs)))


if __name__ == '__main__':
    main()
