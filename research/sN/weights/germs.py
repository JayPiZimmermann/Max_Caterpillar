#!/usr/bin/env python3
"""Exact classes of T-germs modulo the auxiliary germs (weights/germs.py).

A T-germ on n = |T| coordinates is the function
    g(z) = relu(<v, z> + sum_{(i,j) in M} relu(z_i - z_j))
(a "key" (v, M) of vocabulary_search on n variables, v arbitrary integer with
sum 0).  Its class lives in the space of PL functions on R^n modulo
span{linear, relu(z_i - z_j)}.  We also quotient by relu(+-z_i): those have
kinks on z_i = 0 which no translation-invariant function has, so this does
not change any linear relation among the T-germs and max (README.md).

Exactness: vocabulary_search.cell_blocks gives, per cell of the arrangement
{z_i = z_j, z_i = 0}, integer coordinates such that a combination of the
functions vanishes on R^n iff every coordinate vanishes, *provided every kink
of every function lies on a hyperplane recorded by its own coordinates* (the
cell method records the kink direction d of relu(<a,x>) inside each cell,
so it is exact for nested relus whose inner part is linear on each cell).
All linear algebra is over Q with python-flint (fmpq_mat).

class_coords(n, germs) returns (rank, coords, maxcoords): coords[g] is the
coordinate vector (list of Fractions) of the class of germ g in a basis of the
span of all classes and max_n; zero vector = class zero.
"""
import os
import sys
from fractions import Fraction

import flint

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'scripts'))
import vocabulary_search as vs


def _rref_rows(rows, ncols):
    """rref of a list of integer/Fraction rows; returns (list of rows, pivots)."""
    if not rows:
        return [], []
    M = flint.fmpq_mat(len(rows), ncols, [x for r in rows for x in r])
    R, rk = M.rref()
    out, piv = [], []
    for i in range(rk):
        row = [R[i, j] for j in range(ncols)]
        p = next(j for j in range(ncols) if row[j] != 0)
        out.append(row)
        piv.append(p)
    return out, piv


def class_coords(n, germs, modp_rows=False):
    """modp_rows=True keeps only coordinate rows that are independent modulo
    vs.P (EchelonModP); the rational computation then runs on that subset.
    This is sound for "class nonzero / not in a span" only if those rows span
    the full row space over Q, which holds unless P divides a minor: NOT a
    certificate (used only for large n, and cross-checked by verify_tests)."""
    aux = vs.aux_functions(n)
    funcs = [('aux', a) for a in aux] + [('key', g) for g in germs] + [('max',)]
    rowset = set()
    if modp_rows:
        E = vs.EchelonModP(len(funcs))
    for block in vs.cell_blocks(n, funcs):
        for row in block:
            if modp_rows and not E.add(row):
                continue
            rowset.add(tuple(sorted(row.items())))
    rows = sorted(rowset)
    nr = len(rows)
    na = len(aux)
    nf = len(funcs)
    # function x coordinate matrix (integers)
    F = flint.fmpz_mat(nf, nr)
    for r, row in enumerate(rows):
        for j, c in row:
            F[j, r] = c
    A = flint.fmpq_mat(flint.fmpz_mat([[F[i, r] for r in range(nr)] for i in range(na)]))
    RA, ra = A.rref()
    PA = []
    for i in range(ra):
        PA.append(next(j for j in range(nr) if RA[i, j] != 0))
    G = flint.fmpq_mat(flint.fmpz_mat([[F[i, r] for r in range(nr)] for i in range(na, nf)]))
    ng = nf - na
    if ra:
        Gp = flint.fmpq_mat(ng, ra, [G[i, p] for i in range(ng) for p in PA])
        RAs = flint.fmpq_mat(ra, nr, [RA[i, j] for i in range(ra) for j in range(nr)])
        red = G - Gp * RAs
    else:
        red = G
    RG, rg = red.rref()
    PG = []
    for i in range(rg):
        PG.append(next(j for j in range(nr) if RG[i, j] != 0))
    coords = [[Fraction(int(red[i, p].p), int(red[i, p].q)) for p in PG] for i in range(ng)]
    return len(PG), coords[:-1], coords[-1]


if __name__ == '__main__':
    # self-test: max_3 class nonzero, relu(z0 - z1) zero, relu(z0 - z2 + relu(z2 - z1))
    n = 3
    germs = [((1, -1, 0), frozenset()), ((0, 0, 0), frozenset({(0, 1)})),
             ((1, 0, -1), frozenset({(1, 2)})), ((2, -1, -1), frozenset())]
    rk, co, mx = class_coords(n, germs)
    print('rank', rk, 'max', mx)
    for g, c in zip(germs, co):
        print(g, c)
