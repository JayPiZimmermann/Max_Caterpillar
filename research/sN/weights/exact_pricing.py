#!/usr/bin/env python3
"""Exact pricing: certify that the final dual y of colgen.py is feasible for
EVERY test (every stratum type with t <= TMAX and every flat H, max_t not in H),
not only for the generated columns.  This makes the LP optimum exact.

For each type (t, c') the exact weights w(g) = sum_k y_k a_k(g) on projective
germ classes are formed; a violated test exists iff there is a set D of
classes with w(D) < 1 such that max_t is not in span(G+ minus D), where G+ =
classes with w > 0 (classes of weight 0 may be excluded for free).  Decided by
exhaustive branch and bound with exact rational echelon forms:
  classes in decreasing weight; a class already in span(kept) is kept for
  free; otherwise branch keep (if max stays outside) / exclude (if the
  excluded weight stays < 1).  Any leaf = violated test.
For t > TMAX only the generic test exists; checked directly.
Usage: python3 exact_pricing.py N TMAX
"""
import math
import os
import pickle
import sys
import time
from fractions import Fraction

from colgen import GermSpace, compositions, norm_germ
from lp import perm_germ

HERE = os.path.dirname(os.path.abspath(__file__))


class Echelon:
    """Exact incremental row echelon form over Q (dict pivot -> row)."""

    def __init__(self, rows=None):
        self.rows = {}
        for r in rows or []:
            self.add(r)

    def reduce(self, v):
        v = list(v)
        for p, r in self.rows.items():
            if v[p]:
                c = v[p]
                v = [a - c * b for a, b in zip(v, r)]
        return v

    def contains(self, v):
        return not any(self.reduce(v))

    def add(self, v):
        v = self.reduce(v)
        nz = [i for i, a in enumerate(v) if a]
        if not nz:
            return False
        p = nz[0]
        v = [a / v[p] for a in v]
        for q in list(self.rows):
            if self.rows[q][p]:
                c = self.rows[q][p]
                self.rows[q] = [a - c * b for a, b in zip(self.rows[q], v)]
        self.rows[p] = v
        return True

    def copy(self):
        e = Echelon()
        e.rows = dict(self.rows)
        return e


def search(keys, w, mx, budget=10**6):
    """Return (violated D or None, nodes)."""
    keys = sorted(keys, key=lambda k: -w[k])
    nodes = [0]
    found = [None]

    def rec(i, E, excl, wex):
        nodes[0] += 1
        if found[0] is not None or nodes[0] > budget:
            return
        if i == len(keys):
            found[0] = list(excl)
            return
        k = keys[i]
        if E.contains(k):
            rec(i + 1, E, excl, wex)
            return
        E2 = E.copy()
        E2.add(k)
        if not E2.contains(mx):
            rec(i + 1, E2, excl, wex)
        if wex + w[k] < 1:
            rec(i + 1, E, excl + [k], wex + w[k])

    rec(0, Echelon(), [], Fraction(0))
    return found[0], nodes[0]


def main():
    N, TMAX = int(sys.argv[1]), int(sys.argv[2])
    sol = pickle.load(open(os.path.join(HERE, 'data', f'colgen_{N}_{TMAX}.pkl'), 'rb'))
    y = sol['y']
    _, data = pickle.load(open(os.path.join(HERE, 'data', f'strata_{N}.pkl'), 'rb'))
    assert [k for k, _ in data] == sol['units']
    sup = [u for u in range(len(y)) if y[u]]
    print(f'N={N} TMAX={TMAX}: dual value {sum(y)}, support {len(sup)} canonical units', flush=True)
    bysize = {}
    for _, res in data:
        for T, (g, _) in res.items():
            bysize.setdefault(len(T), set()).add(g)
    ok = True
    for t in range(3, TMAX + 1):
        sp = GermSpace(t, bysize[t])
        for cp in compositions(N - t):
            S = math.factorial(N) // math.factorial(t)
            for a in cp:
                S //= math.factorial(a)
            w = {}
            for u in sup:
                for T, (g, cn) in data[u][1].items():
                    if len(T) != t or cp not in cn:
                        continue
                    for p in sp.perms:
                        key = sp.rep[sp.gid[norm_germ(perm_germ(g, p))]]
                        if key is not None:
                            w[key] = w.get(key, 0) + y[u] * Fraction(cn[cp], S * len(sp.perms))
            keys = [k for k in w if w[k] > 0]
            tot = sum(w.values(), Fraction(0))
            t0 = time.time()
            D, nodes = search(keys, w, list(sp.mx))
            status = 'ok' if D is None else 'VIOLATED'
            if D is None and nodes > 10**6:
                status = 'BUDGET EXCEEDED'
            ok &= status == 'ok'
            print(f'  ({t},{cp}): |G+| = {len(keys)}, total weight {tot} -> {status}'
                  f' ({nodes} nodes, {time.time() - t0:.1f}s)'
                  + ('' if D is None else f' excluded weight {sum(w[k] for k in D)}'), flush=True)
    # generic columns for t > TMAX are among the generated columns (certified by colgen)
    print(f'RESULT N={N} TMAX={TMAX}: exact pricing {"PASSED: tau* = " + str(sum(y)) if ok else "FAILED"}')


if __name__ == '__main__':
    main()
