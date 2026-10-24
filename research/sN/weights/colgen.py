#!/usr/bin/env python3
"""Column generation for the covering LP over ALL top-block functionals.

Tests: (P, Lambda) with P a stratum (top block T, |T| = t >= 3, any ordered
partition of the rest, lower ties allowed) and Lambda any linear functional on
T-germ classes with Lambda(max_t) != 0 (README.md, lp.py).  For t <= TMAX we
allow every such Lambda (minimal hit sets = complements of hyperplanes H of the
matroid of germ classes, max_t not in H); for t > TMAX only the generic one.

Symmetric LP: one column per (t, c', H) with H a flat (not containing max_t)
in the space of t-germ classes; unit k's coefficient is
    a_k(t,c',H) = sum_T n(k,T,c')/S(t,c') * (1/t!) #{pi in S_t : pi.g_{k,T} not in H}.

Pricing: given LP duals y (on canonical units), weights w(g) on permuted germ
classes; a violated column is a flat H with max_t not in H and
sum_{g not in H} w(g) < 1.  Found by a big-M MILP over functionals (HiGHS),
then made exact: H := exact span of the germs the MILP kept, greedily
extended (exact rank tests) while max_t stays outside.  Every column used is
therefore an exactly valid test, and the reported primal value is a rigorous
lower bound on tau* (hence on s_N).  Optimality of the final value rests on
the float MILP pricing (reported as such) unless --exact-dual succeeds.

Usage: python3 colgen.py N TMAX [TEXACT] [MODP_FROM]
(MODP_FROM: top sizes t >= MODP_FROM use germs.class_coords(modp_rows=True), not certified.)
"""
import itertools
import math
import os
import pickle
import sys
import time
from fractions import Fraction

import flint
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

from germs import class_coords
from lp import perm_germ
from exactlp import certify_bounds

HERE = os.path.dirname(os.path.abspath(__file__))


def fq(x):
    return flint.fmpq(x.numerator, x.denominator)


def qrank(vecs):
    if not vecs:
        return 0
    return flint.fmpq_mat(len(vecs), len(vecs[0]), [fq(x) for v in vecs for x in v]).rank()


def compositions(n):
    if n == 0:
        yield ()
        return
    for a in range(1, n + 1):
        for rest in compositions(n - a):
            yield (a,) + rest


def norm_germ(g):
    """Same function, pairs oriented i < j: relu(z_i - z_j) = relu(z_j - z_i) + z_i - z_j."""
    v, M = g
    v = list(v)
    out = set()
    for i, j in M:
        if i > j:
            v[i] += 1
            v[j] -= 1
            i, j = j, i
        out.add((i, j))
    return (tuple(v), frozenset(out))


class GermSpace:
    def __init__(self, t, germs, normalize=True, modp_rows=False):
        self.t = t
        self.nf = norm_germ if normalize else (lambda g: g)
        perms = list(itertools.permutations(range(t)))
        allg = sorted({self.nf(perm_germ(g, p)) for g in germs for p in perms}, key=str)
        t0 = time.time()
        self.rank, co, self.mx = class_coords(t, allg, modp_rows=modp_rows)
        self.germs = allg
        self.gid = {g: i for i, g in enumerate(allg)}
        self.co = co
        self.cof = np.array([[float(x) for x in c] for c in co])
        self.mxf = np.array([float(x) for x in self.mx])
        self.perms = perms
        # projective representatives (exactly equal classes up to scalar share membership)
        self.rep = {}
        self.members = {}
        for i, c in enumerate(co):
            if any(c):
                f = next(x for x in c if x)
                key = tuple(x / f for x in c)
            else:
                key = None
            self.rep[i] = key
            self.members.setdefault(key, []).append(i)
        print(f'  t={t}: {len(allg)} permuted germs, rank {self.rank}, '
              f'{len(self.members) - (None in self.members)} projective classes '
              f'({time.time() - t0:.1f}s)', flush=True)

    def extend_flat(self, keep):
        """Exact: basis of span(keep) (max must be outside), greedily extended by
        all projective classes keeping max outside.  Returns frozenset of class
        keys inside H (the hit set is everything else that is nonzero)."""
        basis = []
        for key in keep:
            if qrank(basis + [list(key)]) > len(basis):
                basis.append(list(key))
        if qrank(basis + [list(self.mx)]) == len(basis):
            return None
        inside = set()
        for key in self.members:
            if key is None:
                continue
            if qrank(basis + [list(key)]) == len(basis):
                inside.add(key)
                continue
            if qrank(basis + [list(key), list(self.mx)]) == len(basis) + 2:
                basis.append(list(key))
                inside.add(key)
        return frozenset(inside)


def main():
    N = int(sys.argv[1])
    TMAX = int(sys.argv[2])
    TEXACT = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    global MODP_FROM
    MODP_FROM = int(sys.argv[4]) if len(sys.argv) > 4 else 99
    _, data = pickle.load(open(os.path.join(HERE, 'data', f'strata_{N}.pkl'), 'rb'))
    units = [k for k, _ in data]
    U = len(units)
    print(f'N={N} TMAX={TMAX} canonical units {U}', flush=True)
    bysize = {}
    for _, res in data:
        for T, (g, _) in res.items():
            bysize.setdefault(len(T), set()).add(g)
    spaces = {}
    nonzero = {}
    for t, gs in sorted(bysize.items()):
        if t <= TMAX:
            spaces[t] = GermSpace(t, gs, modp_rows=(t >= MODP_FROM))
            for g in gs:
                nonzero[g] = spaces[t].rep[spaces[t].gid[g]] is not None
        elif t <= TEXACT:
            gs = sorted(gs, key=str)
            _, co, _ = class_coords(t, gs)
            for g, c in zip(gs, co):
                nonzero[g] = any(c)
        else:
            for g in gs:
                nonzero[g] = True
    types = [(t, cp) for t in range(3, N + 1) for cp in compositions(N - t)]
    S = {}
    for t, cp in types:
        s = math.factorial(N) // math.factorial(t)
        for a in cp:
            s //= math.factorial(a)
        S[(t, cp)] = s
    # per unit, per type: {permuted gid: weight} (t <= TMAX) or scalar (t > TMAX)
    prof = [dict() for _ in range(U)]
    for u, (k, res) in enumerate(data):
        for T, (g, cn) in res.items():
            t = len(T)
            for cp, n in cn.items():
                if t <= TMAX:
                    sp = spaces[t]
                    d = prof[u].setdefault((t, cp), {})
                    for p in sp.perms:
                        q = sp.gid[sp.nf(perm_germ(g, p))]
                        if sp.rep[q] is not None:
                            d[q] = d.get(q, 0) + Fraction(n, S[(t, cp)] * len(sp.perms))
                elif nonzero[g]:
                    prof[u][(t, cp)] = prof[u].get((t, cp), 0) + Fraction(n, S[(t, cp)])
    cols = []      # (t, cp, inside-set or None)
    colvec = []    # exact coefficient column (list of Fractions over units)

    def column(t, cp, inside):
        sp = spaces.get(t)
        v = []
        for u in range(U):
            e = prof[u].get((t, cp))
            if e is None:
                v.append(Fraction(0))
            elif isinstance(e, dict):
                v.append(sum((w for q, w in e.items()
                               if inside is None or sp.rep[q] not in inside), Fraction(0)))
            else:
                v.append(e)
        return v

    for t, cp in types:
        cols.append((t, cp, None))
        colvec.append(column(t, cp, None))
    it = 0
    while True:
        it += 1
        A = [[colvec[j][u] for j in range(len(cols))] for u in range(U)]
        Af = np.array([[float(x) for x in r] for r in A])
        res = linprog(-np.ones(len(cols)), A_ub=Af, b_ub=np.ones(U), bounds=(0, None), method='highs')
        y = -res.ineqlin.marginals
        val = -res.fun
        print(f' iter {it}: columns {len(cols)}, LP value {val:.9f}, dual support {int((y > 1e-9).sum())}', flush=True)
        added = 0
        for t in sorted(spaces):
            sp = spaces[t]
            for cp in compositions(N - t):
                w = {}
                for u in np.nonzero(y > 1e-12)[0]:
                    e = prof[u].get((t, cp))
                    if e:
                        for q, a in e.items():
                            w[q] = w.get(q, 0.0) + y[u] * float(a)
                # aggregate by projective class
                wk = {}
                for q, a in w.items():
                    wk[sp.rep[q]] = wk.get(sp.rep[q], 0.0) + a
                keys = [k for k, a in wk.items() if a > 1e-12]
                if not keys:
                    continue
                if sum(wk[k] for k in keys) < 1 - 1e-9:
                    continue    # generic column already present
                # MILP: lambda in R^r, mx.lambda = 1, |g.lambda| <= Mb * b_g
                r = sp.rank
                G = np.array([[float(x) for x in k] for k in keys])
                n = len(keys)
                Mb = 1e3
                c = np.concatenate([np.zeros(r), np.array([wk[k] for k in keys])])
                cons = [LinearConstraint(np.concatenate([sp.mxf, np.zeros(n)])[None, :], 1, 1),
                        LinearConstraint(np.hstack([G, -Mb * np.eye(n)]), -np.inf, 0),
                        LinearConstraint(np.hstack([-G, -Mb * np.eye(n)]), -np.inf, 0)]
                integ = np.concatenate([np.zeros(r), np.ones(n)])
                bnd = Bounds(np.concatenate([-1e3 * np.ones(r), np.zeros(n)]),
                             np.concatenate([1e3 * np.ones(r), np.ones(n)]))
                m = milp(c, constraints=cons, integrality=integ, bounds=bnd,
                         options={'time_limit': 300, 'mip_rel_gap': 1e-9})
                if m.x is None:
                    print(f'   pricing ({t},{cp}): MILP status {m.status}', flush=True)
                    continue
                if m.fun >= 1 - 1e-7:
                    continue
                keep = [keys[i] for i in range(n) if m.x[r + i] < 0.5]
                inside = sp.extend_flat(keep)
                if inside is None:
                    print(f'   pricing ({t},{cp}): MILP solution not exact, skipped', flush=True)
                    continue
                cols.append((t, cp, inside))
                colvec.append(column(t, cp, inside))
                added += 1
                print(f'   + column ({t},{cp}) MILP cost {m.fun:.6f}, |inside| {len(inside)}', flush=True)
        if not added:
            break
    # exact certification
    A = [[colvec[j][u] for j in range(len(cols))] for u in range(U)]
    Af = np.array([[float(x) for x in r] for r in A])
    res = linprog(-np.ones(len(cols)), A_ub=Af, b_ub=np.ones(U), bounds=(0, None), method='highs')
    lo, hi, x, yq = certify_bounds(A, res.x, -res.ineqlin.marginals)
    val = lo
    print(f'RESULT N={N} TMAX={TMAX}: LP over generated columns: exact primal {lo} = {float(lo):.6f},'
          f' exact dual {hi} = {float(hi):.6f}' + (' (CERTIFIED EQUAL)' if lo == hi else '')
          + f'; C(N,3)/2 = {Fraction(math.comb(N, 3), 2)}')
    print('  primal weights:')
    for j, cl in enumerate(cols):
        if x[j]:
            print('   ', cl[0], cl[1], 'generic' if cl[2] is None else f'flat |inside|={len(cl[2])}', x[j])
    print('  dual support:')
    for u in range(U):
        if yq[u]:
            print('    h=', units[u][0], 'M=', sorted(units[u][1]), 'y=', yq[u])
    with open(os.path.join(HERE, 'data', f'colgen_{N}_{TMAX}.pkl'), 'wb') as f:
        pickle.dump({'inside_germs': [None if c[2] is None else [spaces[c[0]].germs[i] for key in c[2] for i in spaces[c[0]].members[key]] for c in cols], 'cols': cols, 'x': x, 'y': yq, 'lo': lo, 'hi': hi, 'units': units, 'colvec': colvec}, f)


if __name__ == '__main__':
    main()
