#!/usr/bin/env python3
"""Independent check of the covering LP primal solution found by colgen.py.

Different instrument from colgen/strata/germs:
  * the REAL dictionary (vocabulary_search.dictionary, all labels, not only
    canonical units), evaluated DIRECTLY at actual points p + z (no use of
    condition (a), of v_T, or of the cell-coordinate machinery);
  * every labelled stratum of the column's type, at an explicit point p with
    top block T at 0 and lower blocks at -S*B^j (lower ties respected);
  * moves z supported on T, integer sample points; linear algebra on the
    sample matrix modulo the prime 2^61 - 1 (flint nmod_mat).  Over Q the
    statements "max not in H" and "U_k not in H" on samples are sound; modulo
    a random large prime they hold with overwhelming probability (cross-check
    instrument, not a certificate).
For a column (t, c', H) and each labelled stratum P and each permutation pi
of T, the flat H_pi = span(aux germs at p, inside germs composed with pi) is
built on the samples; the column is a valid test at (P, pi) iff max is not in
H_pi on samples (SOUND: a rank increase on samples is a rank increase on R^n).
Unit k counts as hit iff U_k is not in H_pi on samples (sound for "hit";
"not hit" is sampled evidence only).
The script then recomputes each unit's load sum_j x_j * (hit fraction) and
checks that it is <= 1 for every unit of the real dictionary.

Usage: python3 verify_tests.py N TMAX [samples] [seed] [canonical]
"""
import itertools
import math
import os
import pickle
import random
import sys
from fractions import Fraction

import flint

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'scripts'))
import vocabulary_search as vs

HERE = os.path.dirname(os.path.abspath(__file__))
PR = 2**61 - 1


def relu(t):
    return t if t > 0 else 0


def eval_germ(g, zT):
    v, M = g
    return relu(sum(a * b for a, b in zip(v, zT)) + sum(relu(zT[i] - zT[j]) for i, j in M))


def ordered_partitions(items, comp):
    if not comp:
        yield ()
        return
    for b in itertools.combinations(items, comp[0]):
        rest = [o for o in items if o not in b]
        for tail in ordered_partitions(rest, comp[1:]):
            yield (b,) + tail


def main():
    N = int(sys.argv[1])
    TMAX = int(sys.argv[2])
    NS = int(sys.argv[3]) if len(sys.argv) > 3 else 500
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 7
    sol = pickle.load(open(os.path.join(HERE, 'data', f'colgen_{N}_{TMAX}.pkl'), 'rb'))
    cols, x = sol['cols'], sol['x']
    if len(sys.argv) > 5 and sys.argv[5] == 'canonical':
        # loads are S_N-invariant (tests are averaged over all labelled strata
        # and all permutations of T), so canonical representatives suffice
        from strata import canonical_units
        units = canonical_units(N)
    else:
        K0, _ = vs.dictionary(N)
        units = sorted((k for k in K0 if not vs.is_auxiliary(k)), key=str)
    aux = vs.aux_functions(N)
    print(f'N={N}: dictionary units {len(units)}; columns with x>0: {sum(1 for v in x if v)}', flush=True)
    # germ lists of each projective class: recompute from colgen spaces
    from colgen import GermSpace
    _, data = pickle.load(open(os.path.join(HERE, 'data', f'strata_{N}.pkl'), 'rb'))
    bysize = {}
    for _, res in data:
        for T, (g, _) in res.items():
            bysize.setdefault(len(T), set()).add(g)
    spaces = {} if 'inside_germs' in sol else {t: GermSpace(t, gs, normalize=False) for t, gs in bysize.items() if t <= TMAX and any(
        x[j] and cols[j][0] == t and cols[j][2] is not None for j in range(len(cols)))}
    rng = random.Random(seed)
    Sc, Bc = 10**6, 100
    load = [Fraction(0)] * len(units)
    for j, (t, cp, inside) in enumerate(cols):
        if not x[j]:
            continue
        if inside is None:
            ingerms = []
        elif 'inside_germs' in sol:
            ingerms = sol['inside_germs'][j]
        else:
            sp = spaces[t]
            ingerms = [sp.germs[i] for key in inside for i in sp.members[key]]
        Z = [tuple(rng.randint(-1000, 1000) for _ in range(t)) for _ in range(NS)]
        perms = list(itertools.permutations(range(t))) if inside is not None else [tuple(range(t))]
        hits = [0] * len(units)
        ntest = 0
        for T in itertools.combinations(range(N), t):
            rest = [o for o in range(N) if o not in T]
            for blocks in ordered_partitions(rest, cp):
                p = [0] * N
                for jb, b in enumerate(blocks):
                    for o in b:
                        p[o] = -Sc * Bc ** (jb + 1)
                pts = []
                for z in Z:
                    q = list(p)
                    for a, tt in enumerate(T):
                        q[tt] += z[a]
                    pts.append(q)
                auxcols = [[vs.eval_aux(a, q) for q in pts] for a in aux] + [[1] * NS]
                maxcol = [max(q) for q in pts]
                ucols = [[vs.eval_key(k, q) for q in pts] for k in units]
                UM = flint.nmod_mat([[ucols[u][i] % PR for u in range(len(units))] for i in range(NS)], PR)
                for pi in perms:
                    Hcols = auxcols + [[eval_germ(g, tuple(z[pi[a]] for a in range(t))) for z in Z]
                                       for g in ingerms]
                    HT = flint.nmod_mat([[c % PR for c in col] for col in Hcols], PR)
                    W, nul = HT.nullspace()              # columns of W: kernel of HT
                    Wt = flint.nmod_mat([[int(W[i, c]) for i in range(NS)] for c in range(nul)], PR)
                    mres = Wt * flint.nmod_mat([[v % PR] for v in maxcol], PR)
                    if all(int(mres[i, 0]) == 0 for i in range(nul)):
                        print('  INVALID TEST: max in H on samples', (t, cp), T, blocks, pi)
                        return
                    UR = Wt * UM
                    for u in range(len(units)):
                        if any(int(UR[i, u]) != 0 for i in range(nul)):
                            hits[u] += 1
                    ntest += 1
        for u in range(len(units)):
            load[u] += x[j] * Fraction(hits[u], ntest)
        print(f'  column {j} type ({t},{cp}) {"generic" if inside is None else "flat"}: '
              f'{ntest} labelled tests valid (max outside H); x = {x[j]}; '
              f'max hit fraction {Fraction(max(hits), ntest)}', flush=True)
    mx = max(load)
    arg = [units[u] for u in range(len(units)) if load[u] == mx][:3]
    print(f'RESULT N={N}: primal value sum x = {sum(x)}; max unit load (independent) = {mx} '
          f'-> {"FEASIBLE" if mx <= 1 else "INFEASIBLE"}; bound |K| >= {sum(x) / max(mx, 1)}')
    print('  tight units (first 3):', arg)


if __name__ == '__main__':
    main()
