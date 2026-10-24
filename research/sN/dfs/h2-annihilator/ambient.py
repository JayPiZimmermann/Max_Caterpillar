"""Ambient space W_N for the translation-invariant part of V_N.

Objects (exact, integer):
  TI functions on R^N / R*1.  Braid cell C_pi = {x_pi0 < ... < x_pi(N-1)},
  gap coordinates t_j = x_pi(j) - x_pi(j-1), j = 1..N-1 (t >= 0 on the cell).
  A unit U_k restricted to C_pi is relu(g . t) with g_j = a . r_j, where a is the
  gradient of A_k on the cell and r_j = 1_{pi(j..N-1)}.

  W_N(D) := continuous functions f on R^N/R1 such that on each cell
     f = L_pi(t) + sum_{p in D_pi} c_{pi,p} relu(p . t),
  with D_pi a prescribed set of primitive integer vectors of mixed sign on the
  cell (default: the kink directions of the units on that cell).
  Because the cell is simplicial and the kink hyperplanes are distinct, the
  per-cell coordinates (L_pi, c_pi) are unique; continuity across a braid wall
  t_j = 0 is: equal linear parts on the wall and equal total coefficient of each
  wall kink direction (restriction of relu to the wall cone, again unique).

V^TI_N = span(units, relu(x_i - x_j), TI linear functions) is a subspace of W_N.
"""
import itertools
import os
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import vocabulary_search as vs  # noqa: E402


def units_of(N):
    K0, _ = vs.dictionary(N)
    return sorted(k for k in K0 if not vs.is_auxiliary(k))


def primitive(g):
    d = 0
    for t in g:
        d = gcd(d, abs(t))
    p = tuple(t // d for t in g)
    for t in p:
        if t:
            return (p, d) if t > 0 else (tuple(-s for s in p), -d)
    raise ValueError


def classify(g):
    """relu(g . t) on the orthant t >= 0: returns (kinkdict, linear tuple)."""
    if all(v >= 0 for v in g):
        return {}, tuple(g)
    if all(v <= 0 for v in g):
        return {}, (0,) * len(g)
    p, lam = primitive(g)
    lin = tuple(lam * s for s in p) if lam < 0 else (0,) * len(g)
    return {p: abs(lam)}, lin


def gap_form(a, pi):
    """g_j = a . r_j, r_j = indicator of pi[j:], j = 1..N-1."""
    N = len(pi)
    out = []
    s = 0
    suff = [0] * (N + 1)
    for j in range(N - 1, -1, -1):
        s += a[pi[j]]
        suff[j] = s
    return tuple(suff[j] for j in range(1, N))


def unit_grad(key, pos):
    h, M = key
    a = list(h)
    for i, j in M:
        if pos[i] > pos[j]:
            a[i] += 1
            a[j] -= 1
    return a


def cell_data(N, funcs):
    """funcs: list of ('key', key) | ('pair', i, j) | ('lin', vector a, sum 0)
    | ('max',).  Returns perms and, per function, per cell: (kinkdict, linear)."""
    perms = list(itertools.permutations(range(N)))
    data = []
    for f in funcs:
        row = []
        for pi in perms:
            pos = {v: r for r, v in enumerate(pi)}
            if f[0] == 'key':
                g = gap_form(unit_grad(f[1], pos), pi)
                row.append(classify(g))
            elif f[0] == 'pair':
                a = [0] * N
                a[f[1]], a[f[2]] = 1, -1
                row.append(classify(gap_form(a, pi)))
            elif f[0] == 'lin':
                row.append(({}, gap_form(f[1], pi)))
            elif f[0] == 'max':
                a = [0] * N
                a[pi[-1]] = 1
                a[0] -= 1          # max_N - x_0, translation invariant
                row.append(({}, gap_form(a, pi)))
            elif f[0] == 'relu':   # relu(<a,x>) with a.1 = 0
                row.append(classify(gap_form(f[1], pi)))
            else:
                raise ValueError(f)
        data.append(row)
    return perms, data


class Ambient:
    def __init__(self, N, D):
        """D: list (indexed like perms) of sorted lists of kink primitives."""
        self.N = N
        self.perms = list(itertools.permutations(range(N)))
        self.pidx = {p: i for i, p in enumerate(self.perms)}
        self.D = D
        self.offset = []
        self.kidx = []
        n = 0
        for c, ds in enumerate(D):
            self.offset.append(n)
            self.kidx.append({p: k for k, p in enumerate(ds)})
            n += (N - 1) + len(ds)
        self.nvars = n

    def var_lin(self, c, j):          # j = 0..N-2  (gap coordinate t_{j+1})
        return self.offset[c] + j

    def var_kink(self, c, p):
        return self.offset[c] + self.N - 1 + self.kidx[c][p]

    def vector(self, cells):
        """cells[c] = (kinkdict, linear) -> sparse dict var -> int.  Raises if a
        kink is not allowed."""
        v = {}
        for c, (kd, lin) in enumerate(cells):
            for j, x in enumerate(lin):
                if x:
                    v[self.var_lin(c, j)] = v.get(self.var_lin(c, j), 0) + x
            for p, x in kd.items():
                k = self.var_kink(c, p)
                v[k] = v.get(k, 0) + x
        return v

    def walls(self):
        N = self.N
        for c, pi in enumerate(self.perms):
            for j in range(1, N):          # swap positions j-1, j ; wall t_j = 0
                pi2 = list(pi)
                pi2[j - 1], pi2[j] = pi2[j], pi2[j - 1]
                c2 = self.pidx[tuple(pi2)]
                if c2 > c:
                    yield c, c2, j

    def restrict(self, c, j):
        """Restriction to the wall t_j = 0 of the cell-c basis functions:
        list over variables of (kinkdict, linear) in wall coordinates."""
        N = self.N
        out = []
        drop = j - 1
        for jj in range(N - 1):
            lin = [0] * (N - 1)
            lin[jj] = 1
            del lin[drop]
            out.append((self.var_lin(c, jj), {}, tuple(lin)))
        for p in self.D[c]:
            w = list(p)
            del w[drop]
            kd, lin = classify(tuple(w)) if any(w) else ({}, (0,) * (N - 2))
            out.append((self.var_kink(c, p), kd, lin))
        return out

    def constraints(self):
        rows = []
        for c, c2, j in self.walls():
            eq = {}
            for sign, cc in ((1, c), (-1, c2)):
                for var, kd, lin in self.restrict(cc, j):
                    for l, x in enumerate(lin):
                        if x:
                            eq.setdefault(('L', l), {})
                            eq[('L', l)][var] = eq[('L', l)].get(var, 0) + sign * x
                    for q, x in kd.items():
                        eq.setdefault(('K', q), {})
                        eq[('K', q)][var] = eq[('K', q)].get(var, 0) + sign * x
            for r in eq.values():
                r = {k: x for k, x in r.items() if x}
                if r:
                    rows.append(r)
        return rows


def unit_kink_sets(N, units):
    perms, data = cell_data(N, [('key', k) for k in units])
    D = [set() for _ in perms]
    for row in data:
        for c, (kd, lin) in enumerate(row):
            D[c] |= set(kd)
    return perms, data, [sorted(s) for s in D]


def base_funcs(N):
    fs = [('pair', i, j) for i in range(N) for j in range(N) if i != j]
    for i in range(1, N):
        a = [0] * N
        a[i], a[0] = 1, -1
        fs.append(('lin', tuple(a)))
    return fs
