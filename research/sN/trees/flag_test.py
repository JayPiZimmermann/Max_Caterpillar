#!/usr/bin/env python3
"""Flag invariants of tree germs at an m-tie (research/sN/trees).

For a polytope G (vertex list, integer coordinates indexed by C) and a deletion order
sigma = (i_1, ..., i_{m-2}) of C, define recursively
    tau(G; sigma) = tau(argmin_{p_{i_1}} G; sigma') - tau(argmax_{p_{i_1}} G; sigma'),
and for |C| = 2, C = {j, k}: tau(G) = max p_j - min p_j  (lattice length).
tau is a linear functional on support functions (iterated germ jumps) that kills every
polytope of dimension < m-1 (lineality argument, see PROGRESS.md) and linear functions;
tau(simplex) = 1 for every sigma.
Germ G(a, v, F) = support function of conv(0, v + sum_F [0, e_i - e_j]).
Test: is the all-ones vector in the span of the tau-vectors of a germ family?
Usage: flag_test.py m R mode
"""
import sys, itertools
from fractions import Fraction
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from pn_test import forests, is_ham_path, is_spanning, heads, rank_mod_p
import numpy as np


def tau(G, order, coords):
    """G: list of tuples (full length m); order: remaining deletion order; coords: remaining coords."""
    if len(coords) == 2:
        j = coords[0]
        vals = [p[j] for p in G]
        return max(vals) - min(vals)
    i = order[0]
    rest = [c for c in coords if c != i]
    vals = [p[i] for p in G]
    lo, hi = min(vals), max(vals)
    Gmin = list({p for p in G if p[i] == lo})
    Gmax = list({p for p in G if p[i] == hi})
    return tau(Gmin, order[1:], rest) - tau(Gmax, order[1:], rest)


def pyramid(m, v, F):
    gens = []
    for (i, j) in F:
        g = [0] * m; g[i] += 1; g[j] -= 1
        gens.append(g)
    pts = {tuple([0] * m)}
    for S in itertools.product([0, 1], repeat=len(gens)):
        p = list(v)
        for s, g in zip(S, gens):
            if s:
                p = [x + y for x, y in zip(p, g)]
        pts.add(tuple(p))
    return list(pts)


def orders(m):
    out = []
    for seq in itertools.permutations(range(m), m - 2):
        out.append(seq)
    return out


def tau_vector(m, G, ords):
    return [tau(G, o, list(range(m))) for o in ords]


def main():
    m, R, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    ords = orders(m)
    a = 0
    rest = list(range(1, m))
    Fs = forests(rest)
    sel = {
        'all': lambda F: True,
        'nopath': lambda F: not is_ham_path(F, rest),
        'top': lambda F: is_spanning(F, rest),
        'topnopath': lambda F: is_spanning(F, rest) and not is_ham_path(F, rest),
    }[mode]
    Fs2 = [F for F in Fs if sel(F)]
    rows = []
    for ap in range(m):  # all apices (the family is symmetric; no symmetrisation used here)
        perm = list(range(m)); perm[0], perm[ap] = perm[ap], perm[0]
        for F in Fs2:
            FF = [(perm[i], perm[j]) for i, j in F]
            for v in heads(m, a, R):
                vv = [0] * m
                for t in range(m):
                    vv[perm[t]] = v[t]
                G = pyramid(m, vv, FF)
                rows.append(tau_vector(m, G, ords))
    A = np.array(rows, dtype=np.int64).T  # cols = germs
    one = np.ones((len(ords), 1), dtype=np.int64)
    r1 = rank_mod_p(A); r2 = rank_mod_p(np.concatenate([A, one], axis=1))
    nz = sum(1 for r in rows if any(r))
    print(f'm={m} R={R} mode={mode}: {len(rows)} germs ({nz} with nonzero tau), {len(ords)} flags; '
          f'rank {r1}, with max {r2} -> max {"NOT in" if r2 > r1 else "IN"} span of tau-vectors', flush=True)


if __name__ == '__main__':
    main()
