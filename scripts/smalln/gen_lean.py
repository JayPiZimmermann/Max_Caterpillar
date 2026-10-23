#!/usr/bin/env python3
"""Generate Lean certificates for exact small-N expansions of the maximum.

Input: a JSON expansion (format in README.md).  Output, for an instance named
`Name` (a Lean identifier):

  MaxCaterpillar/SmallN/Name/Defs.lean      right-hand side `rhs`, max helper
  MaxCaterpillar/SmallN/Name/CellsK.lean    cell lemmas and chamber lemmas
  MaxCaterpillar/SmallN/Name.lean           coverage tree, identity, network
  scripts/smalln/out/Name_cover.json        the cover (H-descriptions, signs)

The cover.  Every coordinate comparison x_i <= x_j (and x_i <= 0 when a
term is not translation invariant) is decided first, by an insertion-sort
decision tree of `le_total` splits; its leaves are the closed braid chambers,
and every consecutive inequality of a chamber is literally a hypothesis on
its path.  Inside a chamber every inner function sigma(x_i - x_j) is linear,
so each outer argument is a linear form.  Each chamber is refined by a second
decision tree that splits on `le_total 0 L` for the first outer argument L
whose sign is not yet constant on the current cell.  Cells are kept as exact
V-descriptions (double description in the chamber's simplex coordinates), so
"constant sign" is decided exactly and every split produces two cells with
nonempty interior.  At a leaf every sigma is linear; the identity is checked
here in exact rational arithmetic and in Lean by `linear_combination` after
`relu_eq_self`/`relu_eq_zero` rewrites whose side conditions are closed by
`linarith only` from the cell hypotheses.

usage: python3 scripts/smalln/gen_lean.py input.json [--chunk LEAVES]
"""
import argparse
import itertools
import json
import os
import sys
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
Z = 'z'  # the pseudo-coordinate with value 0


# ------------------------------------------------------------------ input

def load(path):
    js = json.load(open(path))
    N = js['N']
    name = js['name']
    assert name.isidentifier() and name[0].isupper(), 'name must be a capitalized identifier'
    units = []
    for u in js['units']:
        head = [Fraction(t) for t in u['head']]
        assert len(head) == N
        pairs = []
        for p in u['pairs']:
            i, j = int(p[0]), int(p[1])
            w = Fraction(p[2]) if len(p) > 2 else Fraction(1)
            assert i != j and 0 <= i < N and 0 <= j < N
            pairs.append((i, j, w))
        units.append({'coef': Fraction(u['coef']), 'head': head, 'pairs': pairs})
    aux = []
    for a in js.get('aux', []):
        k = a['kind']
        assert k in ('pos', 'neg', 'pair', 'lin')
        t = (k, a['i'], a['j']) if k == 'pair' else (k, a['i'])
        aux.append((Fraction(a['coef']), t))
    return js, name, N, units, aux


# ------------------------------------------------------------ linear forms

def atom_form(N, atom):
    """Linear form (vector over x, and a constant 0) of an inner argument."""
    v = [Fraction(0)] * N
    if atom[0] == 'pair':
        v[atom[1]] += 1
        v[atom[2]] -= 1
    elif atom[0] == 'pos':
        v[atom[1]] = Fraction(1)
    elif atom[0] == 'neg':
        v[atom[1]] = Fraction(-1)
    return v


def unit_atoms(u):
    return [('pair', i, j) for i, j, _ in u['pairs']]


def all_atoms(units, aux):
    seen = []
    for u in units:
        for a in unit_atoms(u):
            if a not in seen:
                seen.append(a)
    for _, t in aux:
        if t[0] in ('pair', 'pos', 'neg') and t not in seen:
            seen.append(t)
    return seen


def chamber_coords(N, order):
    """x_i as linear forms in the gap variables delta_k >= 0 of the chamber
    order[0] <= ... <= order[-1].  Without Z the common translation is
    dropped (all forms used are then translation invariant)."""
    d = len(order) - 1
    R = {}
    if Z in order:
        p = order.index(Z)
        for j, e in enumerate(order):
            r = [0] * d
            if j > p:
                for k in range(p + 1, j + 1):
                    r[k - 1] = 1
            elif j < p:
                for k in range(j + 1, p + 1):
                    r[k - 1] = -1
            if e != Z:
                R[e] = r
    else:
        for j, e in enumerate(order):
            r = [0] * d
            for k in range(1, j + 1):
                r[k - 1] = 1
            R[e] = r
    return R


def to_delta(form, R, d):
    g = [Fraction(0)] * d
    for i, c in enumerate(form):
        if c:
            for k in range(d):
                g[k] += c * R[i][k]
    return g


def sign_in_chamber(form, R, d):
    g = to_delta(form, R, d)
    if all(t >= 0 for t in g):
        return 1
    if all(t <= 0 for t in g):
        return -1
    raise AssertionError('inner argument not of constant sign on a braid chamber')


# --------------------------------------------------- double description

def prim(v):
    """Scale a rational vector to a primitive integer vector (same direction)."""
    den = 1
    for t in v:
        den = den * Fraction(t).denominator // gcd(den, Fraction(t).denominator)
    w = [int(Fraction(t) * den) for t in v]
    g = 0
    for t in w:
        g = gcd(g, abs(t))
    return tuple(t // g for t in w) if g else tuple(w)


def dot(a, b):
    return sum(s * t for s, t in zip(a, b))


class Cone:
    """A pointed polyhedral cone in R^d with its constraints and extreme rays."""

    def __init__(self, cons, rays):
        self.cons = cons
        self.rays = rays

    @staticmethod
    def orthant(d):
        e = [tuple(1 if i == k else 0 for i in range(d)) for k in range(d)]
        return Cone(list(e), list(e))

    def sign(self, g):
        vals = [dot(g, r) for r in self.rays]
        if all(v >= 0 for v in vals):
            return 1
        if all(v <= 0 for v in vals):
            return -1
        return 0

    def cut(self, g):
        """The cone intersected with {g >= 0} (g changes sign on the cone)."""
        zs = [frozenset(i for i, a in enumerate(self.cons) if dot(a, r) == 0) for r in self.rays]
        vals = [dot(g, r) for r in self.rays]
        pos = [i for i, v in enumerate(vals) if v > 0]
        neg = [i for i, v in enumerate(vals) if v < 0]
        new = [self.rays[i] for i, v in enumerate(vals) if v >= 0]
        for i in pos:
            for j in neg:
                common = zs[i] & zs[j]
                if any(k != i and k != j and common <= zs[k] for k in range(len(self.rays))):
                    continue
                r = tuple(vals[i] * a - vals[j] * b for a, b in zip(self.rays[j], self.rays[i]))
                new.append(prim(r))
        return Cone(self.cons + [tuple(g)], new)


# ------------------------------------------------------------------ cover

class Leaf:
    def __init__(self, splits, signs):
        self.splits = splits     # list of (form over x, sign) on the path inside the chamber
        self.signs = signs       # unit index -> +1 / -1


def unit_form_in_chamber(N, u, atom_sign):
    f = list(u['head'])
    for i, j, w in u['pairs']:
        if atom_sign[('pair', i, j)] > 0:
            f[i] += w
            f[j] -= w
    return f


def refine(N, units, forms, R, d):
    """Decision tree over the outer arguments inside one chamber.
    Returns a nested structure: ('leaf', Leaf) or ('split', form, plus, minus)."""
    deltas = [prim(to_delta(f, R, d)) if any(f) else None for f in forms]

    def rec(cone, splits):
        signs = {}
        for k, g in enumerate(deltas):
            if g is None:
                signs[k] = 1
                continue
            s = cone.sign(g)
            if s == 0:
                gneg = tuple(-t for t in g)
                return ('split', k, rec(cone.cut(g), splits + [(k, 1)]),
                        rec(cone.cut(gneg), splits + [(k, -1)]))
            signs[k] = s
        return ('leaf', Leaf(splits, signs))

    return rec(Cone.orthant(d), [])


def farkas(g, cols):
    """Exact phase-1 simplex (Bland's rule): find y >= 0 with sum_j y_j cols[j] = g.
    Returns the list y (Fractions) or None when infeasible."""
    d, n = len(g), len(cols)
    rows = []
    for i in range(d):
        r = [Fraction(c[i]) for c in cols]
        b = Fraction(g[i])
        if b < 0:
            r, b = [-t for t in r], -b
        rows.append(r + [Fraction(1 if k == i else 0) for k in range(d)] + [b])
    basis = [n + i for i in range(d)]
    m = n + d
    while True:
        # reduced costs of the phase-1 objective (sum of artificials)
        cost = [Fraction(0)] * (m + 1)
        for i, bv in enumerate(basis):
            if bv >= n:
                for j in range(m + 1):
                    cost[j] += rows[i][j]
        enter = next((j for j in range(m) if j not in basis and cost[j] > 0), None)
        if enter is None:
            break
        ratios = [(rows[i][m] / rows[i][enter], basis[i], i) for i in range(d) if rows[i][enter] > 0]
        _, _, piv = min(ratios)
        pv = rows[piv][enter]
        rows[piv] = [t / pv for t in rows[piv]]
        for i in range(d):
            if i != piv and rows[i][enter] != 0:
                f = rows[i][enter]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[piv])]
        basis[piv] = enter
    y = [Fraction(0)] * m
    for i, bv in enumerate(basis):
        y[bv] = rows[i][m]
    if any(y[j] != 0 for j in range(n, m)):
        return None
    return y[:n]


def count_leaves(t):
    return 1 if t[0] == 'leaf' else count_leaves(t[2]) + count_leaves(t[3])


# ------------------------------------------------------------- printing

def q(c):
    c = Fraction(c)
    return str(c.numerator) if c.denominator == 1 else f'{c.numerator}/{c.denominator}'


def xs(i):
    return f'x {i}'


def lin_str(form):
    """Linear form over x with rational coefficients, e.g. `x 1 + 2 * x 3 - x 0`."""
    out = ''
    for i, c in enumerate(form):
        if c == 0:
            continue
        mag = abs(c)
        term = xs(i) if mag == 1 else f'{q(mag)} * {xs(i)}'
        if not out:
            out = term if c > 0 else (f'-{term}' if mag == 1 else f'-({term})')
        else:
            out += (' + ' if c > 0 else ' - ') + term
    return out or '0'


def atom_str(a):
    if a[0] == 'pair':
        return f'relu (x {a[1]} - x {a[2]})'
    if a[0] == 'pos':
        return f'relu (x {a[1]})'
    return f'relu (-x {a[1]})'


def unit_arg_str(u):
    s = lin_str(u['head'])
    for i, j, w in u['pairs']:
        t = atom_str(('pair', i, j))
        if w == 1:
            s += f' + {t}'
        elif w > 0:
            s += f' + {q(w)} * {t}'
        elif w == -1:
            s += f' - {t}'
        else:
            s += f' - {q(-w)} * {t}'
    return s


def sum_str(terms, sep=''):
    """terms: list of (coef, expr string); `sep` is inserted before each + / -."""
    out = ''
    for c, e in terms:
        if c == 0:
            continue
        mag = abs(c)
        t = e if mag == 1 else f'{q(mag)} * {e}'
        if not out:
            out = t if c > 0 else f'-({t})' if mag != 1 else f'-{t}'
        else:
            out += sep + (' + ' if c > 0 else ' - ') + t
    return out or '0'


def aux_expr(t):
    if t[0] == 'lin':
        return f'x {t[1]}'
    return atom_str(t)


def rhs_terms(units, aux):
    terms = [(u['coef'], f'relu ({unit_arg_str(u)})') for u in units]
    terms += [(c, aux_expr(t)) for c, t in aux]
    return terms


def wrap(items, width=96):
    out, cur = [], ''
    for it in items:
        if cur and len(cur) + 1 + len(it) > width:
            out.append(cur)
            cur = it
        else:
            cur = (cur + ' ' + it) if cur else it
    if cur:
        out.append(cur)
    return out


def el_str(e):
    return '0' if e == Z else f'x {e}'


def form_hyp(form, s):
    L = lin_str(form)
    return f'0 ≤ {L}' if s > 0 else f'{L} ≤ 0'


# -------------------------------------------------------------- the tree

def braid_tree(elems):
    """Insertion-sort decision tree over `le_total` comparisons:
    ('cmp', a, e, h, branch a <= e, branch e <= a) or ('chamber', order, hyps),
    hyps[k] naming the path hypothesis order[k] <= order[k+1]."""
    counter = itertools.count(1)

    def insert(sl, cons, rest):
        if not rest:
            return ('chamber', tuple(sl),
                    [cons[(sl[k], sl[k + 1])] for k in range(len(sl) - 1)])
        return place(sl, cons, rest[0], len(sl), None, rest[1:])

    def place(sl, cons, e, pos, h_above, rest):
        # invariant: e <= sl[pos] via hypothesis h_above (when pos < len(sl))
        a = sl[pos - 1]
        h = f'h{next(counter)}'
        nl = sl[:pos] + [e] + sl[pos:]
        c1 = dict(cons)
        if pos < len(sl):
            del c1[(a, sl[pos])]
            c1[(e, sl[pos])] = h_above
        c1[(a, e)] = h
        b1 = insert(nl, c1, rest)
        if pos == 1:
            c2 = dict(cons)
            c2[(e, a)] = h
            b2 = insert([e] + sl, c2, rest)
        else:
            b2 = place(sl, cons, e, pos - 1, h, rest)
        return ('cmp', a, e, h, b1, b2)

    return insert([elems[0]], {}, list(elems[1:]))


def chambers_of(t):
    if t[0] == 'chamber':
        return [t]
    return chambers_of(t[4]) + chambers_of(t[5])


# --------------------------------------------------------- generation

class Gen:
    def __init__(self, path, chunk):
        self.js, self.name, self.N, self.units, self.aux = load(path)
        self.chunk = chunk
        N = self.N
        self.atoms = all_atoms(self.units, self.aux)
        need_z = any(a[0] in ('pos', 'neg') for a in self.atoms) or \
            any(sum(u['head']) != 0 for u in self.units)
        self.elems = list(range(N)) + ([Z] if need_z else [])
        self.ns = f'MaxCaterpillar.SmallN.{self.name}'
        self.dir = os.path.join(ROOT, 'MaxCaterpillar', 'SmallN', self.name)

    # ---- per chamber analysis
    def analyse(self, order):
        N = self.N
        d = len(order) - 1
        R = chamber_coords(N, order)
        atom_sign = {a: sign_in_chamber(atom_form(N, a), R, d) for a in self.atoms}
        forms = [unit_form_in_chamber(N, u, atom_sign) for u in self.units]
        tree = refine(N, self.units, forms, R, d)
        return R, d, atom_sign, forms, tree

    def check_leaf(self, order, atom_sign, forms, leaf):
        """Exact check of the identity on the cell: returns linear_combination data."""
        N = self.N
        top = [e for e in order if e != Z][-1]
        # remainder r = x_top - sum c_k val_k - sum a_t val_t, as a dict over x_i and atoms
        r = {('x', top): Fraction(1)}

        def add(key, c):
            r[key] = r.get(key, Fraction(0)) + c

        for k, u in enumerate(self.units):
            if leaf.signs[k] > 0:
                for i, h in enumerate(u['head']):
                    if h:
                        add(('x', i), -u['coef'] * h)
                for i, j, w in u['pairs']:
                    add(('atom', ('pair', i, j)), -u['coef'] * w)
        for c, t in self.aux:
            if t[0] == 'lin':
                add(('x', t[1]), -c)
            else:
                add(('atom', t), -c)
        mu = {a: r.get(('atom', a), Fraction(0)) for a in self.atoms}
        # substitute atoms by their linear values; the result must vanish
        res = [Fraction(0)] * N
        for key, c in r.items():
            if key[0] == 'x':
                res[key[1]] += c
        for a, c in mu.items():
            if atom_sign[a] > 0:
                f = atom_form(N, a)
                for i in range(N):
                    res[i] += c * f[i]
        if Z not in self.elems:
            # translation invariant: compare modulo nothing; all coefficients must vanish
            pass
        assert all(t == 0 for t in res), ('identity fails on a cell', order, leaf.splits, res)
        return mu

    # ---- Lean emission
    def header(self, imports, doc):
        return '\n'.join(f'import {m}' for m in imports) + f'\n\n/-! {doc} -/\n\n' + \
            'set_option autoImplicit false\nset_option linter.unusedVariables false\n\nnamespace ' + self.ns + '\n\nopen MaxCaterpillar.SmallN\n\n'

    def defs_file(self):
        N = self.N
        terms = rhs_terms(self.units, self.aux)
        body = sum_str(terms, '\n   ')
        s = self.header(['MaxCaterpillar.SmallN.Common'],
                        f'# `{self.name}`: the right-hand side\n\nGenerated by `scripts/smalln/gen_lean.py` '
                        f'from `{self.relsrc}`; do not edit.')
        s += f'/-- The right-hand side of the expansion of `max_{N}`. -/\n'
        s += f'noncomputable def rhs (x : Point {N}) : ℝ :=\n    {body}\n\n'
        hyps = ' '.join(f'(h{i} : x {i} ≤ x t)' for i in range(N))
        s += f'theorem max_eq (x : Point {N}) (t : Fin {N}) {hyps} :\n    Maximum {N} x = x t := by\n'
        s += '  refine maximum_eq_of_le x t fun i => ?_\n  fin_cases i\n'
        s += '  exacts [' + ', '.join(f'h{i}' for i in range(N)) + ']\n\n'
        s += f'end {self.ns}\n'
        return s

    def chain_hyps(self, order):
        return [f'(c{k} : {el_str(order[k])} ≤ {el_str(order[k + 1])})' for k in range(len(order) - 1)]

    def atom_eq(self, a, sgn):
        rhs = lin_str(atom_form(self.N, a)) if sgn > 0 else '0'
        return f'{atom_str(a)} = {rhs}'

    def atom_fact(self, a, sgn, order, ci_names):
        # 0 <= arg or arg <= 0 from the chain: consecutive hypotheses between the two elements
        if a[0] == 'pair':
            lo, hi = (a[2], a[1]) if sgn > 0 else (a[1], a[2])
        elif a[0] == 'pos':
            lo, hi = (Z, a[1]) if sgn > 0 else (a[1], Z)
        else:
            lo, hi = (a[1], Z) if sgn > 0 else (Z, a[1])
        p, r = order.index(lo), order.index(hi)
        hs = ci_names[p:r]
        lem = 'relu_eq_self' if sgn > 0 else 'relu_eq_zero'
        rhs = lin_str(atom_form(self.N, a)) if sgn > 0 else '0'
        tac = f'by linarith only [{", ".join(hs)}]' if hs else 'by linarith only []'
        return f'{lem} ({tac})'

    def sign_cert(self, order, R, d, forms, leaf, k, sgn):
        """Tactic proving 0 <= L_k (sgn > 0) or L_k <= 0 from an exact Farkas
        certificate over the cell hypotheses: a nonnegative combination of the
        chain and split hypotheses that equals sgn * L_k (checked by `ring`)."""
        g = [sgn * t for t in to_delta(forms[k], R, d)]
        cols, proofs, exprs = [], [], []
        for j in range(d):
            cols.append([1 if i == j else 0 for i in range(d)])
            proofs.append(f'sub_nonneg.mpr c{j}')
            exprs.append(f'({el_str(order[j + 1])} - {el_str(order[j])})')
        for t, (kk, st) in enumerate(leaf.splits):
            cols.append([st * v for v in to_delta(forms[kk], R, d)])
            L = lin_str(forms[kk])
            proofs.append(f's{t}' if st > 0 else f'neg_nonneg.mpr s{t}')
            exprs.append(f'({L})' if st > 0 else f'(-({L}))')
        y = farkas(g, cols)
        assert y is not None, ('no Farkas certificate', order, leaf.splits, k)
        terms = []
        for c, pf in zip(y, proofs):
            if c == 0:
                continue
            terms.append(pf if c == 1 else f'mul_nonneg (by norm_num : (0:ℝ) ≤ {q(c)}) ({pf})')
        if not terms:
            key = 'le_refl (0:ℝ)'
        else:
            key = terms[-1]
            for t in reversed(terms[:-1]):
                key = f'add_nonneg ({t}) ({key})'
        if sgn > 0:
            return f'exact le_of_le_of_eq ({key}) (by ring)'
        return f'exact neg_nonneg.mp (le_of_le_of_eq ({key}) (by ring))'

    def leaf_theorem(self, lname, order, atom_sign, forms, leaf, mu, R=None, d=None):
        N = self.N
        top = [e for e in order if e != Z][-1]
        cn = [f'c{k}' for k in range(len(order) - 1)]
        args = self.chain_hyps(order)
        sn = []
        for t, (k, s) in enumerate(leaf.splits):
            args.append(f'(s{t} : {form_hyp(forms[k], s)})')
            sn.append(f's{t}')
        aname = {}
        for n, a in enumerate(self.atoms):
            aname[a] = f'q{n}'
            args.append(f'(q{n} : {self.atom_eq(a, atom_sign[a])})')
        lines = [f'theorem {lname} (x : Point {N})']
        lines.append('    ' + '\n    '.join(wrap(args)) + ' :')
        lines.append(f'    x {top} = rhs x := by')
        lc = []
        for k, u in enumerate(self.units):
            s = leaf.signs[k]
            arg = unit_arg_str(u)
            qs = []
            for i, j, _ in u['pairs']:
                if aname[('pair', i, j)] not in qs:
                    qs.append(aname[('pair', i, j)])
            if s > 0:
                rhs = arg
                lem = 'relu_eq_self'
            else:
                rhs = '0'
                lem = 'relu_eq_zero'
            rw = f'rw [{", ".join(qs)}]; ' if qs else ''
            cert = self.sign_cert(order, R, d, forms, leaf, k, s)
            lines.append(f'  have o{k} : relu ({arg}) = {rhs} :=')
            lines.append(f'    {lem} (by {rw}{cert})')
            lc.append((-u['coef'], f'o{k}'))
        for a in self.atoms:
            if mu[a]:
                lc.append((mu[a], aname[a]))
        comb = ' + '.join(f'({q(c)} : ℝ) * {h}' for c, h in lc if c) or '0'
        lines.append('  unfold rhs')
        lines.append(f'  linear_combination {comb}')
        return '\n'.join(lines) + '\n'

    def subtree_tactic(self, t, forms, cname, leafnames, indent, chain_args, depth=0):
        pad = ' ' * indent
        if t[0] == 'leaf':
            lname = leafnames.pop(0)
            args = ' '.join(chain_args + [f's{i}' for i in range(depth)] +
                            [f'q{n}' for n in range(len(self.atoms))])
            return f'{pad}exact {lname} x {args}\n'
        _, k, plus, minus = t
        L = lin_str(forms[k])
        s = f'{pad}rcases le_total 0 ({L}) with s{depth} | s{depth}\n'
        s += f'{pad}· ' + self.subtree_tactic(plus, forms, cname, leafnames, indent + 2, chain_args,
                                              depth + 1).lstrip()
        s += f'{pad}· ' + self.subtree_tactic(minus, forms, cname, leafnames, indent + 2, chain_args,
                                              depth + 1).lstrip()
        return s

    def run(self):
        N = self.N
        self.relsrc = os.path.relpath(self.path, ROOT)
        tree = braid_tree(self.elems)
        chambers = chambers_of(tree)
        cover = []
        files = []          # list of (filename, text)
        cur, cur_leaves, chunk_id = [], 0, 0
        chamber_name = {}
        stats = {'chambers': len(chambers), 'leaves': 0}

        def flush():
            nonlocal cur, cur_leaves, chunk_id
            if not cur:
                return
            text = self.header([f'MaxCaterpillar.SmallN.{self.name}.Defs'],
                               f'# `{self.name}`: cells, chunk {chunk_id}\n\nGenerated by '
                               f'`scripts/smalln/gen_lean.py` from `{self.relsrc}`; do not edit.')
            text += ''.join(cur) + f'end {self.ns}\n'
            files.append((f'Cells{chunk_id}', text))
            chunk_id += 1
            cur, cur_leaves = [], 0

        for ci, (_, order, _) in enumerate(chambers):
            R, d, atom_sign, forms, sub = self.analyse(order)
            leaves = []

            def collect(t):
                if t[0] == 'leaf':
                    leaves.append(t[1])
                else:
                    collect(t[2])
                    collect(t[3])
            collect(sub)
            stats['leaves'] += len(leaves)
            cname = f'chamber{ci}'
            chamber_name[order] = (cname, chunk_id)
            text = []
            lnames = []
            cells = []
            for li, leaf in enumerate(leaves):
                mu = self.check_leaf(order, atom_sign, forms, leaf)
                lname = f'cell{ci}_{li}'
                lnames.append(lname)
                text.append(self.leaf_theorem(lname, order, atom_sign, forms, leaf, mu, R, d) + '\n')
                cells.append({
                    'lean': lname,
                    'H': [[str(c) for c in forms[k]] + [s] for k, s in leaf.splits],
                    'unit_signs': [leaf.signs[k] for k in range(len(self.units))]})
            cover.append({'chamber': [str(e) for e in order], 'lean': cname,
                          'atom_signs': {atom_str(a): s for a, s in atom_sign.items()},
                          'cells': cells})
            top = [e for e in order if e != Z][-1]
            # chamber lemma
            chain = self.chain_hyps(order)
            cn = [f'c{k}' for k in range(len(order) - 1)]
            p = order.index(top)
            maxargs = []
            for i in range(N):
                q_ = order.index(i)
                hs = cn[q_:p]
                maxargs.append(f'(by linarith only [{", ".join(hs)}])' if hs else '(le_refl _)')
            c = [f'theorem {cname} (x : Point {N})', '    ' + ' '.join(chain) + ' :',
                 f'    Maximum {N} x = rhs x := by',
                 f'  rw [max_eq x {top} ' + ' '.join(maxargs) + ']']
            for n, a in enumerate(self.atoms):
                c.append(f'  have q{n} : {self.atom_eq(a, atom_sign[a])} :=')
                c.append(f'    {self.atom_fact(a, atom_sign[a], order, cn)}')
            body = self.subtree_tactic(sub, forms, cname, list(lnames), 2, cn)
            text.append('\n'.join(c) + '\n' + body + '\n')
            if cur and cur_leaves + len(leaves) > self.chunk:
                flush()
                chamber_name[order] = (cname, chunk_id)
            cur.extend(text)
            cur_leaves += len(leaves)
        flush()

        # root file: coverage tree, identity, network
        def emit_braid(t, indent):
            pad = ' ' * indent
            if t[0] == 'chamber':
                cname = chamber_name[t[1]][0]
                return f'{pad}exact {cname} x {" ".join(t[2])}\n'
            _, a, e, h, b1, b2 = t
            s = f'{pad}rcases le_total ({el_str(a)}) ({el_str(e)}) with {h} | {h}\n'
            s += f'{pad}· ' + emit_braid(b1, indent + 2).lstrip()
            s += f'{pad}· ' + emit_braid(b2, indent + 2).lstrip()
            return s

        imports = [f'MaxCaterpillar.SmallN.{self.name}.{f}' for f, _ in files]
        root = self.header(imports, self.root_doc(stats))
        root += f'/-- Every point lies in a cell: the braid chambers are covered by an\n'
        root += f'insertion-sort tree of `le_total` splits, each chamber by its own tree. -/\n'
        root += f'theorem identity (x : Point {N}) : Maximum {N} x = rhs x := by\n'
        root += emit_braid(tree, 2) + '\n'
        root += self.explicit_and_network()
        root += f'end {self.ns}\n'
        files.append(('ROOT', root))
        stats['chunks'] = len(files) - 1
        return files, cover, stats

    def root_doc(self, stats):
        N = self.N
        kind = 'caterpillar functions' if self.caterpillar_valid() else 'second-layer neurons'
        return (f'# `{self.name}`: an exact expansion of `max_{N}` with {len(self.units)}\n'
                f'{kind}\n\nGenerated by `scripts/smalln/gen_lean.py` from `{self.relsrc}`; '
                f'do not edit.\nSource of the data: {self.js.get("source", "?")}.\n\n'
                f'The identity is proved on {stats["leaves"]} closed polyhedral cells inside '
                f'{stats["chambers"]} braid chambers.')

    def caterpillar_valid(self):
        for u in self.units:
            if any(h.denominator != 1 for h in u['head']) or sum(u['head']) != 0:
                return False
            ps = [(i, j) for i, j, _ in u['pairs']]
            if any(w != 1 for _, _, w in u['pairs']) or len(set(ps)) != len(ps):
                return False
        return True

    def explicit_and_network(self):
        N = self.N
        terms = rhs_terms(self.units, self.aux)
        body = sum_str(terms, '\n     ')
        s = f'/-- **The identity, explicitly.** -/\n'
        s += f'theorem max_identity (x : Point {N}) :\n    Maximum {N} x =\n      {body} :=\n'
        s += '  identity x\n\n'
        if any(t[0] not in ('lin', 'pair') for _, t in self.aux):
            return s      # sigma(+-x_i) is not a feature of the paper's first layer for i > 0
        m = len(self.units)
        sumN = f'Fin.sum_univ_{["zero", "one", "two", "three", "four", "five", "six", "seven", "eight"][N]}'
        s += '/-! ## The network -/\n\nset_option linter.unnecessarySeqFocus false\nset_option linter.unreachableTactic false\n\n'
        avars = ' '.join(f'a{i}' for i in range(N))
        alist = ', '.join(f'a{i}' for i in range(N))
        for i in range(N):
            s += f'theorem cv{i} ({avars} : ℚ) : (![{alist}] : Fin {N} → ℚ) {i} = a{i} := rfl\n\n'
        for k, u in enumerate(self.units):
            head = ', '.join(f'({q(h)} : ℚ)' if h < 0 or h.denominator != 1 else q(h) for h in u['head'])
            hs = ', '.join(f'({q(w)}, {i}, {j})' for i, j, w in u['pairs'])
            s += f'/-- Neuron {k}. -/\nnoncomputable def u{k} : Neuron {N} := ⟨{q(u["coef"])}, ![{head}], [{hs}]⟩\n\n'
            s += f'theorem u{k}_eval (x : Point {N}) :\n    (u{k}.coef : ℝ) * relu (u{k}.arg x) =\n      '
            s += f'{sum_str([(u["coef"], "relu (" + unit_arg_str(u) + ")")])} := by\n'
            s += f'  have h : u{k}.arg x = {unit_arg_str(u)} := by\n'
            cvs = ', '.join(f'cv{i}' for i in range(N))
            s += f'    simp [u{k}, Neuron.arg, {sumN}, {cvs}] <;> ring\n'
            s += f'  rw [h]\n  simp only [u{k}]\n  push_cast\n  ring\n\n'
        s += f'noncomputable def neurons : List (Neuron {N}) := [{", ".join(f"u{k}" for k in range(m))}]\n\n'
        aux = []
        for c, t in self.aux:
            if t[0] == 'pair':
                aux.append(f'({q(c)}, .pair {t[1]} {t[2]})')
            else:
                aux.append(f'({q(c)}, .{t[0]} {t[1]})')
        s += f'def auxTerms : List (ℚ × AuxTerm {N}) :=\n  [{", ".join(aux)}]\n\n'
        s += f'theorem expansionEval_eq (x : Point {N}) : expansionEval neurons auxTerms x = rhs x := by\n'
        s += '  simp only [expansionEval, neurons, auxTerms, List.map_cons, List.map_nil, List.sum_cons,\n'
        s += '    List.sum_nil, AuxTerm.eval, ' + ', '.join(f'u{k}_eval' for k in range(m)) + ']\n'
        s += '  unfold rhs\n  push_cast\n  ring\n\n'
        kind = 'caterpillar functions' if self.caterpillar_valid() else 'neurons'
        s += (f'/-- **Network.**  The paper\'s first hidden layer (`firstWidth {N}` neurons) and\n'
              f'{m + 2} neurons in the second hidden layer ({m} {kind} and two for the\n'
              f'linear remainder); rational weights, zero biases. -/\n')
        s += f'theorem max_network :\n    ∃ net : Network {N} (firstWidth {N}) {m + 2},\n'
        s += f'      (∀ x, net.eval x = Maximum {N} x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases :=\n'
        s += f'  network_of_expansion (n := {N - 1}) neurons auxTerms\n'
        s += '    (fun x => (identity x).trans (expansionEval_eq x).symm)\n\n'
        return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('input')
    ap.add_argument('--chunk', type=int, default=150, help='max leaves per chunk file')
    ap.add_argument('--dry', action='store_true', help='only analyse and count cells')
    args = ap.parse_args()
    g = Gen(args.input, args.chunk)
    g.path = os.path.abspath(args.input)
    files, cover, stats = g.run()
    print(f'{g.name}: N={g.N}, units={len(g.units)}, aux={len(g.aux)}, elements={g.elems}, '
          f'chambers={stats["chambers"]}, cells={stats["leaves"]}, chunk files={stats["chunks"]}')
    if args.dry:
        return
    os.makedirs(g.dir, exist_ok=True)
    for old in os.listdir(g.dir):
        if old.startswith('Cells') and old.endswith('.lean'):
            os.remove(os.path.join(g.dir, old))
    for fname, text in files:
        if fname == 'ROOT':
            p = os.path.join(ROOT, 'MaxCaterpillar', 'SmallN', f'{g.name}.lean')
        else:
            p = os.path.join(g.dir, f'{fname}.lean')
        open(p, 'w').write(text)
    open(os.path.join(g.dir, 'Defs.lean'), 'w').write(g.defs_file())
    os.makedirs(os.path.join(HERE, 'out'), exist_ok=True)
    json.dump({'name': g.name, 'N': g.N, 'elements': [str(e) for e in g.elems],
               'chambers': cover}, open(os.path.join(HERE, 'out', f'{g.name}_cover.json'), 'w'))


if __name__ == '__main__':
    main()
