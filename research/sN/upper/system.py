#!/usr/bin/env python3
"""Exact linear system for expansions of max_N (research/sN/upper/system.py).

Columns: units (normalized non-auxiliary dictionary keys), auxiliary functions,
and max_N.  Rows: the cell coordinates of vocabulary_search.cell_blocks, which
are exact: a combination vanishes on R^N iff every row vanishes.  Duplicate
rows are removed.  The matrix is cached as a scipy sparse npz.
"""
import os
import pickle
import sys
import time

import numpy as np
import scipy.sparse as sp

sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, 'data')


def build(N):
    os.makedirs(DATA, exist_ok=True)
    path = os.path.join(DATA, f'system_{N}.pkl')
    if os.path.exists(path):
        with open(path, 'rb') as f:
            return pickle.load(f)
    t0 = time.time()
    K0, _ = vs.dictionary(N)
    units = sorted(k for k in K0 if not vs.is_auxiliary(k))
    aux = vs.aux_functions(N)
    funcs = [('key', k) for k in units] + [('aux', a) for a in aux] + [('max',)]
    seen = set()
    ri, ci, vals = [], [], []
    r = 0
    for block in vs.cell_blocks(N, funcs):
        for row in block:
            key = tuple(sorted(row.items()))
            if key in seen:
                continue
            seen.add(key)
            for j, c in key:
                ri.append(r)
                ci.append(j)
                vals.append(c)
            r += 1
    A = sp.csr_matrix((vals, (ri, ci)), shape=(r, len(funcs)), dtype=np.float64)
    out = dict(N=N, units=units, aux=aux, funcs=funcs, A=A)
    with open(path, 'wb') as f:
        pickle.dump(out, f)
    print(f'N={N}: {len(units)} units, {len(aux)} aux, {r} distinct rows '
          f'({time.time() - t0:.1f}s)', flush=True)
    return out


def certify(N, d, e):
    """Exact check that sum d_k U_k + sum e_a aux_a = max_N on every cell.
    d: {key: Fraction}, e: {aux: Fraction}."""
    from fractions import Fraction
    keys = [k for k in d if d[k] != 0]
    auxs = [a for a in e if e[a] != 0]
    funcs = [('key', k) for k in keys] + [('aux', a) for a in auxs] + [('max',)]
    coeffs = {i: Fraction(d[k]) for i, k in enumerate(keys)}
    coeffs.update({len(keys) + i: Fraction(e[a]) for i, a in enumerate(auxs)})
    coeffs[len(funcs) - 1] = Fraction(-1)
    return vs.verify_relation(N, funcs, coeffs)


if __name__ == '__main__':
    build(int(sys.argv[1]))
