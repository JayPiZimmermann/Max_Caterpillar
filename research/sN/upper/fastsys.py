#!/usr/bin/env python3
"""Vectorized builder of the exact cell system (same rows as system.build).

For every cell (strict order of the N coordinates and 0) and every function
relu(<a(cell), x>) the cell coordinates are: a kink coefficient |lam| at the
primitive direction d of a when a changes sign on the cell (a = lam d, d with
positive first nonzero entry), and a linear part (a if a >= 0 on the cell, 0 if
<= 0, lam d if it changes sign and lam < 0, else 0).  max_N has linear part
e_top.  A combination vanishes on R^N iff all these rows vanish (the functions
are linear on the subcones cut by the kink hyperplanes, and the decomposition
into kinks plus a linear part is unique on the cell).

Usage: python3 fastsys.py N        -> data/fsystem_N.npz (+ keys pickle)
"""
import itertools
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


def functions(N):
    K0, _ = vs.dictionary(N)
    units = sorted(k for k in K0 if not vs.is_auxiliary(k))
    aux = vs.aux_functions(N)
    return units, aux


def build(N, verbose=True):
    os.makedirs(DATA, exist_ok=True)
    path = os.path.join(DATA, f'fsystem_{N}.pkl')
    if os.path.exists(path):
        with open(path, 'rb') as f:
            return pickle.load(f)
    t0 = time.time()
    units, aux = functions(N)
    pairs = [(i, j) for i in range(N) for j in range(i + 1, N)]
    pidx = {p: t for t, p in enumerate(pairs)}
    F = len(units) + len(aux)          # max_N handled separately (last column)
    H = np.zeros((F, N), dtype=np.int64)
    Minc = sp.lil_matrix((F, len(pairs)), dtype=np.int64)
    for r, (h, M) in enumerate(units):
        H[r] = h
        for p in M:
            Minc[r, pidx[p]] = 1
    for t, a in enumerate(aux):
        r = len(units) + t
        if a[0] == 'pos':
            H[r, a[1]] = 1
        elif a[0] == 'neg':
            H[r, a[1]] = -1
        else:
            H[r, a[1]], H[r, a[2]] = 1, -1
    Minc = Minc.tocsr()
    E = np.zeros((len(pairs), N), dtype=np.int64)
    for t, (i, j) in enumerate(pairs):
        E[t, i], E[t, j] = 1, -1
    seen = {}
    ri, ci, vv = [], [], []
    nrow = 0
    ncell = 0
    for order in vs.cells(N):
        ncell += 1
        rays = np.array(vs.cell_rays(N, order), dtype=np.int64)    # N x N
        pos = vs.cell_rank(N, order)
        act = np.array([1 if pos[i] > pos[j] else 0 for (i, j) in pairs], dtype=np.int64)
        Aarg = H + Minc @ (act[:, None] * E)                         # F x N
        vals = Aarg @ rays.T
        nonneg = (vals >= 0).all(1)
        nonpos = (vals <= 0).all(1)
        kink = ~(nonneg | nonpos)
        lin = np.zeros_like(Aarg)
        lin[nonneg] = Aarg[nonneg]
        rows = []
        idx = np.nonzero(kink)[0]
        if len(idx):
            a = Aarg[idx]
            g = np.gcd.reduce(np.abs(a), axis=1)
            first = a[np.arange(len(a)), (a != 0).argmax(1)]
            sgn = np.sign(first)
            d = a // (g * sgn)[:, None]
            lam = g * sgn
            neg = lam < 0
            lin[idx[neg]] = a[neg]
            groups = {}
            for t, r in enumerate(idx):
                groups.setdefault(d[t].tobytes(), []).append((int(r), int(abs(lam[t]))))
            rows.extend(groups.values())
        top = max(range(N), key=lambda i: pos[i])
        for c in range(N):
            nz = np.nonzero(lin[:, c])[0]
            row = [(int(r), int(lin[r, c])) for r in nz]
            if c == top:
                row.append((F, 1))
            if row:
                rows.append(row)
        for row in rows:
            row.sort()
            key = tuple(row)
            if key in seen:
                continue
            seen[key] = nrow
            for j, c in row:
                ri.append(nrow)
                ci.append(j)
                vv.append(c)
            nrow += 1
        if verbose and ncell % 5000 == 0:
            print(f'  cells {ncell}, rows {nrow}, {time.time() - t0:.0f}s', flush=True)
    A = sp.csr_matrix((vv, (ri, ci)), shape=(nrow, F + 1), dtype=np.float64)
    funcs = [('key', k) for k in units] + [('aux', a) for a in aux] + [('max',)]
    out = dict(N=N, units=units, aux=aux, funcs=funcs, A=A)
    with open(path, 'wb') as f:
        pickle.dump(out, f)
    if verbose:
        print(f'N={N}: {len(units)} units, {len(aux)} aux, {nrow} rows, '
              f'{time.time() - t0:.1f}s', flush=True)
    return out


if __name__ == '__main__':
    build(int(sys.argv[1]))
