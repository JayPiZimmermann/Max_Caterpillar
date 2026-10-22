#!/usr/bin/env python3
"""Exact small-arity searches in the caterpillar vocabulary.

Every quantity printed here is a *search lead*.  Ranks are computed from
integer evaluations modulo a large prime, so each rank is a certified LOWER
bound for the rank over the rationals (a sample can only miss directions, and
reduction modulo p can only lower a rank).  No printed equality between
functions, and no printed upper bound on a rank, is a proof: identities
suggested here must be certified separately (see `certify_identity`, which
checks an identity exactly on every cell of a hyperplane arrangement).

Notation follows the paper.  A normalized description is a pair (h, M) with
h an integer vector of coordinate sum zero and M a set of pairs (i, j), i < j,
representing the unit  U_{h,M}(x) = relu(<h,x> + sum_{(i,j) in M} relu(x_i - x_j)).
The auxiliary span A_N is spanned by relu(x_i), relu(-x_i), relu(x_i - x_j).
"""
import argparse
import itertools
import random
from fractions import Fraction

import numpy as np

P = 2_147_483_629  # prime below 2^31; products fit in int64


def relu(t):
    return t if t > 0 else 0


# ---------------------------------------------------------------- dictionary

def caterpillar_descriptions(N):
    """All (pi, S): pi a permutation of range(N), S nonempty subset of 1..r."""
    r = N - 2
    for pi in itertools.permutations(range(N)):
        for size in range(1, r + 1):
            for S in itertools.combinations(range(1, r + 1), size):
                yield pi, frozenset(S)


def edges_and_head(N, pi, S):
    """Edge functions as (parent, child) label pairs and the head (last, apex)."""
    r = N - 2
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((pi[p + 1], pi[j + 1]))
    q = max(S)
    return edges, (pi[q + 1], pi[0])


def vec(N, pairs):
    v = [0] * N
    for a, b in pairs:
        v[a] += 1
        v[b] -= 1
    return tuple(v)


def normalized_faces(N, pi, S):
    """Normalized descriptions of all 3^(N-2) face states of one caterpillar."""
    edges, head = edges_and_head(N, pi, S)
    out = set()
    for states in itertools.product(range(3), repeat=len(edges)):
        lin = [head] + [e for e, s in zip(edges, states) if s == 1]
        hinges = [e for e, s in zip(edges, states) if s == 2]
        M = []
        for a, b in hinges:
            if a > b:                 # reverse: relu(x_a-x_b) = relu(x_b-x_a) + (x_a-x_b)
                lin.append((a, b))
                a, b = b, a
            M.append((a, b))
        out.add((vec(N, lin), frozenset(M)))
    return out


def dictionary(N):
    K0 = set()
    full = set()
    for pi, S in caterpillar_descriptions(N):
        faces = normalized_faces(N, pi, S)
        K0 |= faces
        edges, head = edges_and_head(N, pi, S)
        full.add(normalized_faces_full(N, edges, head))
    return K0, full


def normalized_faces_full(N, edges, head):
    lin = [head]
    M = []
    for a, b in edges:
        if a > b:
            lin.append((a, b))
            a, b = b, a
        M.append((a, b))
    return (vec(N, lin), frozenset(M))


def is_auxiliary(key):
    """Descriptions absorbed by the first layer: empty hinge set, head e_i - e_j."""
    h, M = key
    return not M and sorted(h) == [-1] + [0] * (len(h) - 2) + [1]


def aux_functions(N):
    out = []
    for i in range(N):
        e = [0] * N
        e[i] = 1
        out.append(('pos', i))
        out.append(('neg', i))
    for i in range(N):
        for j in range(i + 1, N):
            out.append(('pair', i, j))
    return out


def eval_key(key, x):
    h, M = key
    return relu(sum(a * b for a, b in zip(h, x)) + sum(relu(x[i] - x[j]) for i, j in M))


def eval_aux(a, x):
    if a[0] == 'pos':
        return relu(x[a[1]])
    if a[0] == 'neg':
        return relu(-x[a[1]])
    return relu(x[a[1]] - x[a[2]])


def eval_max(x):
    return max(x)


# ------------------------------------------------------------- linear algebra

def rank_mod_p(rows):
    """Rank modulo P of an integer matrix given as a list of rows."""
    A = np.array(rows, dtype=np.int64) % P
    m, n = A.shape
    rank = 0
    for col in range(n):
        if rank == m:
            break
        piv = None
        nz = np.nonzero(A[rank:, col])[0]
        if len(nz) == 0:
            continue
        piv = rank + nz[0]
        A[[rank, piv]] = A[[piv, rank]]
        inv = pow(int(A[rank, col]), P - 2, P)
        A[rank] = (A[rank] * inv) % P
        others = np.nonzero(A[:, col])[0]
        for i in others:
            if i != rank:
                A[i] = (A[i] - A[i, col] * A[rank]) % P
        rank += 1
    return rank


def sample_points(N, count, seed, bound=10**6):
    rng = random.Random(seed)
    return [tuple(rng.randint(-bound, bound) for _ in range(N)) for _ in range(count)]


def evaluation_matrix(funcs, points):
    """Columns are functions, rows are points (so column rank = function rank)."""
    return [[f(x) for f in funcs] for x in points]


def sample_rank(funcs, N, extra=40, seed=1):
    pts = sample_points(N, len(funcs) + extra, seed)
    M = evaluation_matrix(funcs, pts)
    return rank_mod_p(M)


# ------------------------------------------------------------------- reports

def report(N, seed=1):
    K0, full = dictionary(N)
    aux = aux_functions(N)
    absorbed = [k for k in K0 if is_auxiliary(k)]
    retained = [k for k in K0 if not is_auxiliary(k)]
    C = sum(__import__('math').comb(N, m) * __import__('math').factorial(m) // 2 * (N - m)
            * m ** (N - m - 1) for m in range(2, N))
    print(f'N={N}: C_N={C}, bound 3^(N-2)C_N={3 ** (N - 2) * C}, '
          f'|K0| (distinct normalized descriptions)={len(K0)}, '
          f'full caterpillars={len(full)}, absorbed={len(absorbed)}, retained={len(retained)}')
    fa = [lambda x, a=a: eval_aux(a, x) for a in aux]
    fk = [lambda x, k=k: eval_key(k, x) for k in retained]
    rA = sample_rank(fa, N, seed=seed)
    rV = sample_rank(fa + fk, N, seed=seed)
    print(f'  rank A_N >= {rA} (|aux|={len(aux)}),  rank V_N >= {rV},  '
          f'q_N = dim V/A >= {rV - rA}')
    return K0, retained, aux


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('N', type=int, nargs='+')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    for N in args.N:
        report(N, args.seed)


if __name__ == '__main__':
    main()


# ----------------------------------------------------- exact cell certificates
#
# On an open order cell of the values {x_0, ..., x_{N-1}, 0} every inner hinge
# relu(x_i - x_j) and every auxiliary function is linear, so each unit equals
# relu(<a, x>) for an integer vector a.  The cell is the simplicial cone
#   x_{b_1} <= ... <= x_{b_z} <= 0 <= x_{a_1} <= ... <= x_{a_m}
# with extreme rays -1_{b_1..b_j} and +1_{a_j..a_m}.  On it, relu(<a,x>) is
# linear when <a, ray> >= 0 for every ray, zero when <= 0 for every ray, and
# otherwise has a kink along a hyperplane meeting the interior.  Functions
# relu(<d,x>) for pairwise non-parallel kinked d, together with the
# coordinates, are linearly independent on the open cone.  Hence a linear
# combination vanishes on R^N iff, on every cell, all kink coefficients and the
# linear part vanish.  `cell_coordinates` returns exactly these coordinates.

def cells(N):
    """All strict orders of the N coordinates and the value 0 ('Z')."""
    for order in itertools.permutations(list(range(N)) + ['Z']):
        yield order


def cell_rays(N, order):
    z = order.index('Z')
    below, above = order[:z], order[z + 1:]
    rays = []
    for j in range(1, len(below) + 1):
        r = [0] * N
        for i in below[:j]:
            r[i] = -1
        rays.append(tuple(r))
    for j in range(len(above)):
        r = [0] * N
        for i in above[j:]:
            r[i] = 1
        rays.append(tuple(r))
    return rays


def cell_rank(N, order):
    """Position of each coordinate in the order (larger = larger value)."""
    return {v: k for k, v in enumerate(order)}


def primitive(a):
    from math import gcd
    g = 0
    for t in a:
        g = gcd(g, abs(t))
    d = tuple(t // g for t in a)
    for t in d:
        if t:
            if t < 0:
                return tuple(-s for s in d), -g
            return d, g
    raise ValueError('zero vector')


def relu_linear_on_cell(a, rays):
    """Coordinates of relu(<a,x>) on the cell: (kink dict, linear vector)."""
    N = len(a)
    vals = [sum(s * t for s, t in zip(a, r)) for r in rays]
    if all(v >= 0 for v in vals):
        return {}, tuple(a)
    if all(v <= 0 for v in vals):
        return {}, (0,) * N
    d, lam = primitive(a)           # a = lam * d, lam may be negative
    lin = tuple(lam * t for t in d) if lam < 0 else (0,) * N
    return {d: abs(lam)}, lin


def key_arg_on_cell(key, pos):
    h, M = key
    a = list(h)
    for i, j in M:
        if pos[i] > pos[j]:
            a[i] += 1
            a[j] -= 1
    return tuple(a)


def coordinates_of(N, order, rays, pos, func):
    """func is ('key', key), ('aux', aux) or ('max',)."""
    if func[0] == 'key':
        return relu_linear_on_cell(key_arg_on_cell(func[1], pos), rays)
    if func[0] == 'max':
        top = max(range(N), key=lambda i: pos[i])
        lin = [0] * N
        lin[top] = 1
        return {}, tuple(lin)
    a = func[1]
    v = [0] * N
    if a[0] == 'pos':
        v[a[1]] = 1
    elif a[0] == 'neg':
        v[a[1]] = -1
    else:
        v[a[1]], v[a[2]] = 1, -1
    return relu_linear_on_cell(tuple(v), rays)


def cell_blocks(N, funcs):
    """Yield, per cell, the exact coordinate block: a list of rows, each row a
    dict {function index: integer}.  The union of all rows is a matrix whose
    kernel is exactly the space of linear relations among `funcs` on R^N."""
    for order in cells(N):
        rays = cell_rays(N, order)
        pos = cell_rank(N, order)
        kinks, lins = {}, [dict() for _ in range(N)]
        for idx, f in enumerate(funcs):
            kd, lin = coordinates_of(N, order, rays, pos, f)
            for d, c in kd.items():
                kinks.setdefault(d, {})
                kinks[d][idx] = kinks[d].get(idx, 0) + c
            for i, c in enumerate(lin):
                if c:
                    lins[i][idx] = lins[i].get(idx, 0) + c
        yield list(kinks.values()) + [row for row in lins if row]


class EchelonModP:
    """Incremental row echelon basis modulo P (rank = exact lower bound)."""

    def __init__(self, ncols):
        self.n = ncols
        self.rows = {}               # pivot column -> normalized row (np array)

    def add(self, row):
        v = np.zeros(self.n, dtype=np.int64)
        for j, c in row.items():
            v[j] = c % P
        for piv in sorted(self.rows):
            if v[piv]:
                v = (v - v[piv] * self.rows[piv]) % P
        nz = np.nonzero(v)[0]
        if len(nz) == 0:
            return False
        piv = int(nz[0])
        v = (v * pow(int(v[piv]), P - 2, P)) % P
        for q in list(self.rows):
            if self.rows[q][piv]:
                self.rows[q] = (self.rows[q] - self.rows[q][piv] * v) % P
        self.rows[piv] = v
        return True

    def rank(self):
        return len(self.rows)


def exact_rank_lower(N, funcs):
    E = EchelonModP(len(funcs))
    for block in cell_blocks(N, funcs):
        for row in block:
            E.add(row)
    return E


def verify_relation(N, funcs, coeffs):
    """Exact check, over the integers/rationals, that sum coeffs[i]*funcs[i] = 0
    on all of R^N.  `coeffs` maps indices to Fractions or ints."""
    for block in cell_blocks(N, funcs):
        for row in block:
            if sum(Fraction(c) * coeffs.get(i, 0) for i, c in row.items()) != 0:
                return False
    return True


def rational_reconstruct(a, m=P):
    """Smallest-height fraction congruent to a modulo m (Wang's algorithm)."""
    a %= m
    bound = int((m // 2) ** 0.5)
    r0, r1, s0, s1 = m, a, 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        raise ValueError('rational reconstruction failed')
    return Fraction(r1, s1)


def kernel_certificate(N, funcs, E=None):
    """Return (rank, kernel) where rank is an exact lower bound (mod-p rank) and
    `kernel` is a list of rational relations each verified exactly on R^N.  The
    relations are in echelon form on the free columns, hence independent, so
    rank_Q <= len(funcs) - len(kernel).  Equality of the two bounds certifies
    the exact rank."""
    if E is None:
        E = exact_rank_lower(N, funcs)
    pivots = sorted(E.rows)
    free = [j for j in range(len(funcs)) if j not in E.rows]
    kernel = []
    for f in free:
        v = {f: Fraction(1)}
        for p in pivots:
            c = int(E.rows[p][f])
            if c:
                v[p] = -rational_reconstruct(c)
        if not verify_relation(N, funcs, v):
            raise ValueError('lifted relation failed exact verification')
        kernel.append(v)
    return E.rank(), kernel


def exact_expansion(N, units):
    """Solve max_N = sum_k d_k U_k + sum_a e_a aux_a over Q (mod-p solve with
    rational reconstruction), then verify the identity exactly on every cell.
    Returns (d, e) or None if no exact expansion exists on this support."""
    aux = aux_functions(N)
    funcs = [('key', k) for k in units] + [('aux', a) for a in aux] + [('max',)]
    rk, ker = kernel_certificate(N, funcs)
    m = len(funcs) - 1
    for v in ker:
        if v.get(m, 0) != 0:
            scale = -1 / v[m]
            coeff = {i: c * scale for i, c in v.items() if i != m}
            d = {units[i]: coeff.get(i, Fraction(0)) for i in range(len(units))}
            e = {aux[i - len(units)]: coeff.get(i, Fraction(0))
                 for i in range(len(units), m)}
            rel = dict(coeff)
            rel[m] = Fraction(-1)
            assert verify_relation(N, funcs, rel)
            return d, e
    return None


def excluded_by_rank(N, units, seed=5):
    """Certify max_N not in span(units + aux): an exact lower bound on the rank
    of the extended family that exceeds the number of spanning functions."""
    aux = aux_functions(N)
    fs = [lambda x, k=k: eval_key(k, x) for k in units] + \
         [lambda x, a=a: eval_aux(a, x) for a in aux] + [eval_max]
    return sample_rank(fs, N, extra=20, seed=seed) == len(fs)


def excluded_exactly(N, units):
    """Exact exclusion: max_N is in span(units + aux) iff an exact expansion
    exists; `exact_expansion` returns None only when the certified kernel of
    the family has no relation involving max_N, i.e. max_N is not in the span
    (the kernel is complete because the mod-p rank lower bound matches)."""
    aux = aux_functions(N)
    funcs = [('key', k) for k in units] + [('aux', a) for a in aux] + [('max',)]
    rk, ker = kernel_certificate(N, funcs)
    assert rk + len(ker) == len(funcs)       # rank and kernel certified exactly
    return all(v.get(len(funcs) - 1, 0) == 0 for v in ker)


def rref_mod_p(M):
    """Reduced row echelon form modulo P of a dense integer matrix; returns the
    reduced matrix and the pivot columns."""
    A = np.array(M, dtype=np.int64) % P
    m, n = A.shape
    pivots, r = [], 0
    for c in range(n):
        if r == m:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), P - 2, P)) % P
        col = A[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - np.outer(col[nzr], A[r])) % P
        pivots.append(c)
        r += 1
    return A[:r], pivots


def cell_matrix_blocks(N, funcs):
    """Integer cell-coordinate rows as dense int64 blocks, one per cell."""
    for block in cell_blocks(N, funcs):
        B = np.zeros((len(block), len(funcs)), dtype=np.int64)
        for r, row in enumerate(block):
            for j, c in row.items():
                B[r, j] = c
        yield B


def exact_rank_fast(N, funcs, extra=60, seed=11):
    """Exact rank of `funcs` on R^N: the rank of a random integer evaluation
    matrix modulo P is a certified lower bound; the kernel of that matrix is
    lifted to integer relations which are verified exactly on every cell, a
    certified upper bound.  Returns (rank, verified) with verified=True iff the
    bounds agree."""
    pts = sample_points(N, len(funcs) + extra, seed, bound=50)
    fs = []
    for f in funcs:
        if f[0] == 'key':
            fs.append(lambda x, k=f[1]: eval_key(k, x))
        elif f[0] == 'aux':
            fs.append(lambda x, a=f[1]: eval_aux(a, x))
        else:
            fs.append(eval_max)
    R, piv = rref_mod_p([[g(x) for g in fs] for x in pts])
    rank = len(piv)
    free = [j for j in range(len(funcs)) if j not in set(piv)]
    K = np.zeros((len(funcs), len(free)), dtype=object)
    from math import lcm
    for t, fcol in enumerate(free):
        vec = {fcol: Fraction(1)}
        for r, pc in enumerate(piv):
            c = int(R[r, fcol])
            if c:
                vec[pc] = -rational_reconstruct(c)
        den = 1
        for v in vec.values():
            den = lcm(den, v.denominator)
        for j, v in vec.items():
            K[j, t] = int(v * den)
    Kint = K.astype(np.int64)
    assert np.array_equal(Kint.astype(object), K), 'kernel entries overflow int64'
    if not free:
        return rank, True
    bound = int(np.abs(Kint).sum(axis=0).max())
    for B in cell_matrix_blocks(N, funcs):
        assert int(np.abs(B).max(initial=0)) * bound < 2 ** 62
        if np.any(B @ Kint):
            return rank, False
    return rank, True
