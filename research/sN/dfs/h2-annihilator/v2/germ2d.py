"""Exact 2D germs of V^TI_N at a point x0 of a codim-2 face of the global fan.

V^TI_N = span(units U_k, relu(x_i-x_j), TI linear).  Global fan = braid
hyperplanes + kink hyperplanes K_N (all a.x = 0, a.1 = 0).
At x0 (integer, sum arbitrary; TI), let Hs = hyperplanes through x0.  If
rank(Hs) = 2 (mod 1) x0 lies in the relative interior of a codim-2 face; the
transversal quotient is 2-dimensional.  We pick the plane
P = {z : z.1 = 0, z.y = 0 for y in a basis of span(x0, ...)}? -- simpler: P is
spanned by two integer vectors u, v with Hs . (span) generic; the germ of f is
psi(r) = f(B x0 + r) - f(B x0) on the 2k rays r = P ∩ H (both signs).
Exact integers throughout (Fraction for nullspaces).
"""
import itertools
import os
import sys
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import vocabulary_search as vs  # noqa
from ambient import units_of  # noqa
from hyperplanes import global_hyperplanes  # noqa


def relu(t):
    return t if t > 0 else 0


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def prim(v):
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    return tuple(x // g for x in v) if g else tuple(v)


def nullspace(rows, n):
    """Rational basis of {z in Q^n : rows z = 0}."""
    M = [[Fraction(x) for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        z = [Fraction(0)] * n
        z[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            z[pc] = -M[i][fc]
        basis.append(z)
    return basis


def rank(rows):
    if not rows:
        return 0
    n = len(rows[0])
    return n - len(nullspace(rows, n))


def intvec(z):
    den = 1
    for x in z:
        den = den * x.denominator // gcd(den, x.denominator)
    return prim([int(x * den) for x in z])


class Germs:
    def __init__(self, N):
        self.N = N
        self.units = units_of(N)
        hp = os.path.join(HERE, f'hyps_{N}.pkl')
        if os.path.exists(hp):
            import pickle
            H = pickle.load(open(hp, 'rb'))
            Bd = sorted(tuple(1 if r == i else -1 if r == j else 0 for r in range(N))
                        for i in range(N) for j in range(i + 1, N))
        else:
            H, Bd = global_hyperplanes(N, self.units)
        self.kink = H
        self.braid = Bd
        self.hyps = H + Bd
        self.funcs = [('u', k) for k in self.units] + \
            [('p', i, j) for i in range(N) for j in range(N) if i < j] + \
            [('l', i) for i in range(1, N)]

    def ev(self, f, x):
        if f[0] == 'u':
            return vs.eval_key(f[1], x)
        if f[0] == 'p':
            return relu(x[f[1]] - x[f[2]])
        if f[0] == 'l':
            return x[f[1]] - x[0]
        if f[0] == 'max':
            return max(x)
        if f[0] == 'fn':
            return f[1](x)
        raise ValueError

    def face(self, x0):
        return [h for h in self.hyps if dot(h, x0) == 0]

    def rays2d(self, x0):
        """Hyperplanes through x0 and the 2k transversal ray vectors in cyclic
        order.  Plane P = {z : z.1 = 0, z . w = 0 for w in W0} where W0 spans
        the face directions' complement... we take P ⊂ {z.1=0} as the set
        orthogonal to a basis of the face span F = {z.1=0, h.z=0 for h in Hs}."""
        N = self.N
        Hs = self.face(x0)
        F = nullspace([[1] * N] + [list(h) for h in Hs], N)      # face span
        assert len(F) == N - 3, (x0, len(F))
        Pb = nullspace([[1] * N] + [[int(c) for c in intvec(f)] for f in F], N)
        assert len(Pb) == 2
        u, v = intvec(Pb[0]), intvec(Pb[1])
        rays = []
        for h in Hs:
            # z = s u + t v with h.z = 0  -> (s,t) = (h.v, -h.u)
            s, t = dot(h, v), -dot(h, u)
            z = prim([s * a + t * b for a, b in zip(u, v)])
            for sg in (1, -1):
                rays.append((tuple(sg * c for c in z), h, (sg * s, sg * t)))
        import math
        rays.sort(key=lambda r: math.atan2(r[2][1], r[2][0]))
        return Hs, u, v, rays

    def germ(self, f, x0, rays, B):
        base = [B * c for c in x0]
        f0 = self.ev(f, base)
        return [self.ev(f, [a + b for a, b in zip(base, r[0])]) - f0 for r in rays]


def weights_from_values(vals, rays):
    """2D PL homogeneous psi given on rays r_i (cyclic) -> weights w_i such
    that psi = lin + sum_i w_i * (bump at ray i) ... we return the 'second
    difference' w_i = psi(r_{i-1}) * det(r_i, r_{i+1}) + psi(r_{i+1}) *
    det(r_{i-1}, r_i) - psi(r_i) * det(r_{i-1}, r_{i+1}) normalised: zero iff
    psi is linear on the sector r_{i-1}..r_{i+1}."""
    n = len(rays)
    out = []
    for i in range(n):
        a, b, c = rays[i - 1][2], rays[i][2], rays[(i + 1) % n][2]
        det = lambda p, q: p[0] * q[1] - p[1] * q[0]
        out.append(vals[i - 1] * det(b, c) + vals[(i + 1) % n] * det(a, b)
                   - vals[i] * det(a, c))
    return out
