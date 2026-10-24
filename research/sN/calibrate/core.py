"""Shared exact machinery for calibrating s_N at small N.

Functions on R^N handled here:
  units  U_k = relu(<h,x> + sum_{(i,j) in M} relu(x_i - x_j))  (retained keys of
         scripts/vocabulary_search.dictionary, i.e. not auxiliary),
  aux    relu(x_i), relu(-x_i), relu(x_i - x_j)  (i < j),
  max_N.

Coordinates: integer point evaluations.  A *functional* is an integer vector y
on a list of integer points P; y(f) = sum_p y_p f(p).  Every functional is a
genuine linear functional on functions, so a cut derived from one is valid no
matter whether P separates the span:
  if y(aux) = 0 for all aux and y(max_N) != 0, then every expansion
  max_N = sum_{k in K} d_k U_k + R must contain some k with y(U_k) != 0.
All such checks are done with Python integers (exact).
"""
import itertools
import os
import random
import sys
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import vocabulary_search as vs  # noqa: E402

P = 2_147_483_629


def units_of(N):
    K0, _ = vs.dictionary(N)
    return sorted(k for k in K0 if not vs.is_auxiliary(k))


def normalize(h, pairs):
    """Normalized key of relu(<h,x> + sum relu(x_a - x_b)) for arbitrary pairs."""
    h = list(h)
    M = []
    for a, b in pairs:
        if a > b:
            h[a] += 1
            h[b] -= 1
            a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))


def permute_key(key, perm):
    """Key of x -> U_key(x o perm^{-1}): coordinate i is renamed perm[i]."""
    h, M = key
    N = len(h)
    h2 = [0] * N
    for i in range(N):
        h2[perm[i]] = h[i]
    return normalize(h2, [(perm[a], perm[b]) for a, b in M])


def unit_perm_table(N, units):
    idx = {k: i for i, k in enumerate(units)}
    perms = list(itertools.permutations(range(N)))
    T = np.zeros((len(perms), len(units)), dtype=np.int32)
    for p, perm in enumerate(perms):
        for i, k in enumerate(units):
            T[p, i] = idx[permute_key(k, perm)]
    return perms, T


def aux_list(N):
    return vs.aux_functions(N)


# ------------------------------------------------------------ evaluation

def eval_units_matrix(units, pts):
    """Integer matrix (len(pts) x len(units)) of exact unit values (int64)."""
    X = np.array(pts, dtype=np.int64)
    out = np.zeros((len(pts), len(units)), dtype=np.int64)
    for c, (h, M) in enumerate(units):
        s = X @ np.array(h, dtype=np.int64)
        for i, j in M:
            s = s + np.maximum(X[:, i] - X[:, j], 0)
        out[:, c] = np.maximum(s, 0)
    return out


def eval_aux_matrix(N, pts):
    X = np.array(pts, dtype=np.int64)
    cols = []
    for a in aux_list(N):
        if a[0] == 'pos':
            cols.append(np.maximum(X[:, a[1]], 0))
        elif a[0] == 'neg':
            cols.append(np.maximum(-X[:, a[1]], 0))
        else:
            cols.append(np.maximum(X[:, a[1]] - X[:, a[2]], 0))
    return np.stack(cols, axis=1)


def eval_max(pts):
    return np.array(pts, dtype=np.int64).max(axis=1)


def random_points(N, count, seed, bound=60):
    rng = random.Random(seed)
    return [tuple(rng.randint(-bound, bound) for _ in range(N)) for _ in range(count)]


# ------------------------------------------------------------ mod-p algebra

def rref_mod_p(A):
    A = np.array(A, dtype=np.int64) % P
    m, n = A.shape
    piv, r = [], 0
    for c in range(n):
        if r == m:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + nz[0]
        if p != r:
            A[[r, p]] = A[[p, r]]
        A[r] = (A[r] * pow(int(A[r, c]), P - 2, P)) % P
        col = A[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            # (col * row) may overflow int64: reduce via object-free trick
            A[nzr] = (A[nzr] - mulmod_outer(col[nzr], A[r])) % P
        piv.append(c)
        r += 1
    return A[:r], piv


def mulmod_outer(u, v):
    """(u[:,None] * v[None,:]) mod P without int64 overflow (P < 2^31)."""
    # split v into 16-bit halves: u*v = u*vh*2^16 + u*vl, each < 2^47
    vh, vl = v >> 16, v & 0xFFFF
    a = (np.outer(u, vh) % P) * 65536 % P
    b = np.outer(u, vl) % P
    return (a + b) % P


def independent_rows(A):
    """Indices of a maximal set of rows independent mod P (greedy)."""
    R, piv = rref_mod_p(np.array(A).T)
    return piv


def rational_reconstruct(a):
    return vs.rational_reconstruct(int(a), P)


# ------------------------------------------------------------ exact checks

def functional_values(y, E):
    """Exact y^T E with Python ints (E integer ndarray, y list of ints)."""
    E = np.asarray(E)
    tot = [0] * E.shape[1]
    for p, w in enumerate(y):
        if w:
            row = E[p]
            for c in range(E.shape[1]):
                v = int(row[c])
                if v:
                    tot[c] += w * v
    return tot


def verify_expansion(N, units, coeffs_units, coeffs_aux):
    """Exact identity max_N = sum d_k U_k + sum e_a aux_a on every cell."""
    aux = aux_list(N)
    funcs = [('key', k) for k in units] + [('aux', a) for a in aux] + [('max',)]
    rel = {}
    for i, k in enumerate(units):
        if coeffs_units.get(k, 0):
            rel[i] = Fraction(coeffs_units[k])
    for j, a in enumerate(aux):
        if coeffs_aux.get(a, 0):
            rel[len(units) + j] = Fraction(coeffs_aux[a])
    rel[len(funcs) - 1] = Fraction(-1)
    return vs.verify_relation(N, funcs, rel)
