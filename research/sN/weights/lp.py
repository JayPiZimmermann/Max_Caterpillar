#!/usr/bin/env python3
"""Optimal locality weights: the covering LP over (stratum, functional) pairs.

Setting (README.md).  A test is a pair (P, Lambda): P a stratum of the braid
arrangement (ordered set partition with top block T, |T| >= 3) and Lambda a
linear functional on germs at a generic point of P, depending only on moves
of the top block, that kills the auxiliary germs and has Lambda(max) != 0.
Unit k "hits" the test if Lambda(U_k) != 0, which requires (a): A_k == 0 on
P, and then Lambda(T-germ of k) != 0.  Every expansion of max_N must contain
a unit hitting every test, so for every probability measure mu on tests
    |K| >= 1 / max_k mu{tests hit by k}.
The best such bound is the fractional covering number
    tau* = max sum_t x_t  s.t.  sum_{t hit by k} x_t <= 1 (all units k), x >= 0.
The problem is S_N-symmetric, so an optimal x is symmetric; we use one
variable per symmetry class of tests and canonical units only.

Functional families:
  F1  (generic) Lambda generic among functionals killing the aux germs:
      hits iff (a) and the T-germ class is nonzero.
  F2  (all functionals, t = |T| = 3 only): Lambda vanishing on a hyperplane H
      of the matroid of T-germ classes, max not in H: hits iff (a) and the
      class is not in H.  Minimal hit sets = complements of hyperplanes.
      Orbits of H under S_3 are averaged.

Exactness: counts n(k,T,c') are exact integers (strata.py), germ classes are
exact over Q (germs.py, |T| <= TMAX_EXACT); for larger |T| we conservatively
declare every germ nonzero (more hits => smaller LP value => still a valid
lower bound).  The LP is solved by HiGHS in floating point, then a rational
primal x and dual y are reconstructed and both certified exactly (Fractions):
x feasible, y feasible, equal objectives => exact optimum.

Usage: python3 lp.py N [F1|F2] [tmax_exact]
"""
import itertools
import math
import os
import pickle
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

from germs import class_coords

HERE = os.path.dirname(os.path.abspath(__file__))


def perm_germ(g, p):
    """Germ g composed with the position permutation: new position i <- old p[i]."""
    v, M = g
    t = len(v)
    inv = {p[i]: i for i in range(t)}
    return (tuple(v[p[i]] for i in range(t)), frozenset((inv[i], inv[j]) for i, j in M))


def rank_of(vecs):
    if not vecs:
        return 0
    import flint
    m = flint.fmpq_mat(len(vecs), len(vecs[0]), [flint.fmpq(x.numerator, x.denominator) for v in vecs for x in v])
    return m.rank()


def hyperplane_hitsets(coords, mx):
    """All minimal hit sets {i : coords[i] not in H}, H a matroid hyperplane
    of {coords} u {mx} not containing mx."""
    r = rank_of([list(c) for c in coords] + [list(mx)])
    # projectively distinct nonzero classes
    reps = {}
    for i, c in enumerate(coords):
        if any(c):
            f = next(x for x in c if x)
            reps.setdefault(tuple(x / f for x in c), []).append(i)
    keys = list(reps)
    out = set()
    for S in itertools.combinations(keys, r - 1):
        base = [list(s) for s in S]
        if rank_of(base) < r - 1:
            continue
        if rank_of(base + [list(mx)]) == r - 1:
            continue
        inside = [kk for kk in keys if rank_of(base + [list(kk)]) == r - 1]
        hit = frozenset(i for kk in keys if kk not in inside for i in reps[kk])
        out.add(hit)
    return r, sorted(out, key=sorted)


def certify(A, x, y):
    """A: list of rows (Fractions) units x columns.  Check A x <= 1, x >= 0,
    A^T y >= 1, y >= 0, sum x == sum y."""
    m, n = len(A), len(A[0])
    assert all(v >= 0 for v in x) and all(v >= 0 for v in y)
    for i in range(m):
        assert sum(A[i][j] * x[j] for j in range(n) if x[j]) <= 1, ('primal', i)
    for j in range(n):
        assert sum(A[i][j] * y[i] for i in range(m) if y[i]) >= 1, ('dual', j)
    assert sum(x) == sum(y), (sum(x), sum(y))
    return sum(x)


def exact_from_float(A, res_x, res_y, tol=1e-9):
    """Rational optimum from the float solution: solve the basis exactly."""
    import flint
    m, n = len(A), len(A[0])
    S = [j for j in range(n) if res_x[j] > tol]
    R = [i for i in range(m) if res_y[i] > tol]
    # primal: rows R tight on support S; dual: columns S tight on support R
    def solve(rows, cols, Mget):
        # least-norm exact solve of Mget(rows, cols) z = 1 via normal equations
        Mm = flint.fmpq_mat(len(rows), len(cols), [flint.fmpq(Mget(i, j).numerator, Mget(i, j).denominator) for i in rows for j in cols])
        Mt = Mm.transpose()
        G = Mt * Mm
        ones = flint.fmpq_mat(len(rows), 1, [1] * len(rows))
        rhs = Mt * ones
        # pick independent columns
        rk = G.rank()
        if rk < len(cols):
            raise ValueError('degenerate basis')
        z = G.solve(rhs)
        return [Fraction(int(z[k, 0].p), int(z[k, 0].q)) for k in range(len(cols))]
    xs = solve(R, S, lambda i, j: A[i][j])
    ys = solve(S, R, lambda j, i: A[i][j])
    x = [Fraction(0)] * n
    for j, v in zip(S, xs):
        x[j] = v
    y = [Fraction(0)] * m
    for i, v in zip(R, ys):
        y[i] = v
    return x, y


def build(N, family, tmax_exact):
    _, data = pickle.load(open(os.path.join(HERE, 'data', f'strata_{N}.pkl'), 'rb'))
    # germs by size; exact classes
    bysize = {}
    for _, res in data:
        for T, (g, _) in res.items():
            bysize.setdefault(len(T), set()).add(g)
    nonzero = {}
    info = {}
    hit3 = None
    for t, gs in sorted(bysize.items()):
        gs = sorted(gs, key=str)
        if t <= tmax_exact:
            if t == 3 and family == 'F2':
                allg = sorted({perm_germ(g, p) for g in gs for p in itertools.permutations(range(3))}, key=str)
                rk, co, mx = class_coords(3, allg)
                gid = {g: i for i, g in enumerate(allg)}
                r, hits = hyperplane_hitsets(co, mx)
                info['F2'] = (rk, len(hits))
                hit3 = (gid, hits)
                for g, c in zip(allg, co):
                    nonzero[g] = any(c)
            else:
                rk, co, mx = class_coords(t, gs)
                for g, c in zip(gs, co):
                    nonzero[g] = any(c)
            info[t] = ('exact', rk, sum(nonzero[g] for g in gs), len(gs))
        else:
            for g in gs:
                nonzero[g] = True
            info[t] = ('conservative', None, len(gs), len(gs))
    # columns
    comps = []
    for t in range(3, N + 1):
        def compositions(n):
            if n == 0:
                yield ()
                return
            for a in range(1, n + 1):
                for rest in compositions(n - a):
                    yield (a,) + rest
        for cp in compositions(N - t):
            comps.append((t, cp))
    cols = []
    for t, cp in comps:
        if t == 3 and family == 'F2':
            for hi in range(len(hit3[1])):
                cols.append((t, cp, hi))
        else:
            cols.append((t, cp, None))
    colidx = {c: j for j, c in enumerate(cols)}
    nstr = {}
    for t, cp in comps:
        s = math.factorial(N) // math.factorial(t)
        for a in cp:
            s //= math.factorial(a)
        nstr[(t, cp)] = s
    A = []
    perms3 = list(itertools.permutations(range(3)))
    for key, res in data:
        row = [Fraction(0)] * len(cols)
        for T, (g, cnts) in res.items():
            t = len(T)
            for cp, n in cnts.items():
                if t == 3 and family == 'F2':
                    gid, hits = hit3
                    pg = [gid[perm_germ(g, p)] for p in perms3]
                    for hi, hs in enumerate(hits):
                        frac = Fraction(sum(1 for q in pg if q in hs), 6)
                        if frac:
                            row[colidx[(t, cp, hi)]] += Fraction(n) * frac / nstr[(t, cp)]
                elif nonzero[g]:
                    row[colidx[(t, cp, None)]] += Fraction(n, nstr[(t, cp)])
        A.append(row)
    return data, cols, A, info, hit3


def solve(N, family='F1', tmax_exact=5, quiet=False):
    data, cols, A, info, hit3 = build(N, family, tmax_exact)
    m, n = len(A), len(cols)
    Af = np.array([[float(v) for v in r] for r in A])
    res = linprog(-np.ones(n), A_ub=Af, b_ub=np.ones(m), bounds=(0, None), method='highs')
    xf = res.x
    yf = -res.ineqlin.marginals
    x, y = exact_from_float(A, xf, yf)
    val = certify(A, x, y)
    if not quiet:
        print(f'N={N} family={family}: units(canonical)={m} columns={n} germ info={info}')
        print(f'  LP optimum tau* = {val} = {float(val):.6f}   (C(N,3)/2 = {Fraction(math.comb(N, 3), 2)})')
        print('  optimal weights x (column: value):')
        for j, c in enumerate(cols):
            if x[j]:
                print('   ', c, x[j])
        sup = [i for i in range(m) if y[i]]
        print(f'  dual support: {len(sup)} canonical units; y values:', sorted(set(y[i] for i in sup)))
        for i in sup[:12]:
            k = data[i][0]
            print('    unit h=', k[0], 'M=', sorted(k[1]), 'y=', y[i])
    return val, cols, x, y, A, data


if __name__ == '__main__':
    N = int(sys.argv[1])
    fam = sys.argv[2] if len(sys.argv) > 2 else 'F1'
    tm = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    solve(N, fam, tm)
