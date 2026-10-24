"""EXACT check of a restricted-model identity
    max_N(x) = sum_k d_k relu(<w_k, Phi(x)>) + R(x),
Phi(x) = (x_0..x_{N-1}, relu(x_i - x_j) for i<j in lexicographic order),
R in span(relu(x_i), relu(-x_i), relu(x_i-x_j)).

All functions are linear on each cell of the arrangement {x_i = x_j} u {x_i = 0}
(cells = strict orders of the N coordinates and 0), except relu(<w,Phi>), which is
relu of a linear form on each cell.  On a cell (a simplicial cone with rays r_m)
we write each function as  linear part + sum over kink directions of c * relu(<n,.>),
n primitive integer with first nonzero entry positive.  An identity holds on the
cell iff linear parts and kink coefficients agree (kinks through the open cell
are linearly independent from linear functions and from each other).
Exact rational arithmetic throughout.
The outer coefficients d and R are solved exactly by the caller or passed in.
"""
import itertools
from fractions import Fraction
from math import gcd


def cells(N):
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


def pairs(N):
    return list(itertools.combinations(range(N), 2))


def arg_on_cell(w, N, pos):
    """Linear form of <w, Phi(x)> on the cell (pos = rank of each coordinate)."""
    a = [Fraction(t) for t in w[:N]]
    for c, (i, j) in zip(w[N:], pairs(N)):
        if pos[i] > pos[j]:
            a[i] += c
            a[j] -= c
    return a


def primitive(a):
    """a (Fractions) = lam * n, n primitive integer, first nonzero of n positive."""
    den = 1
    for t in a:
        den = den * t.denominator // gcd(den, t.denominator)
    ints = [int(t * den) for t in a]
    g = 0
    for t in ints:
        g = gcd(g, abs(t))
    n = [t // g for t in ints]
    lam = Fraction(g, den)
    for t in n:
        if t:
            if t < 0:
                n = [-s for s in n]
                lam = -lam
            break
    return tuple(n), lam


def relu_on_cell(a, rays):
    vals = [sum(s * t for s, t in zip(a, r)) for r in rays]
    N = len(a)
    if all(v >= 0 for v in vals):
        return {}, list(a)
    if all(v <= 0 for v in vals):
        return {}, [Fraction(0)] * N
    n, lam = primitive(a)
    lin = [lam * t for t in n] if lam < 0 else [Fraction(0)] * N
    return {n: abs(lam)}, lin


def check(N, W, d, Rcoef):
    """W: list of weight vectors (len N + C(N,2)), d: outer coefficients,
    Rcoef: dict with keys ('pos',i), ('neg',i), ('pair',i,j) -> coefficient.
    Returns list of failing cells (empty iff identity holds on R^N)."""
    bad = []
    for order in cells(N):
        pos = {v: k for k, v in enumerate(order)}
        rays = cell_rays(N, order)
        kinks = {}
        lin = [Fraction(0)] * N
        for w, dk in zip(W, d):
            kd, l = relu_on_cell(arg_on_cell(w, N, pos), rays)
            for n, c in kd.items():
                kinks[n] = kinks.get(n, 0) + dk * c
            lin = [x + dk * y for x, y in zip(lin, l)]
        for key, c in Rcoef.items():
            l = [Fraction(0)] * N
            if key[0] == 'pos' and pos[key[1]] > pos['Z']:
                l[key[1]] = Fraction(1)
            elif key[0] == 'neg' and pos[key[1]] < pos['Z']:
                l[key[1]] = Fraction(-1)
            elif key[0] == 'pair' and pos[key[1]] > pos[key[2]]:
                l[key[1]] = Fraction(1)
                l[key[2]] = Fraction(-1)
            lin = [x + c * y for x, y in zip(lin, l)]
        top = max(range(N), key=lambda i: pos[i])
        lin[top] -= 1
        if any(lin) or any(c != 0 for c in kinks.values()):
            bad.append(order)
    return bad


if __name__ == '__main__':
    # control: max_4 = d - b ... with one neuron (variables a,b,c,d = 0,1,2,3):
    # max4 = x1 + relu(x0-x1) + relu(x3 - x1 + relu(x2-x3) - relu(x0-x1))
    N = 4
    P = pairs(N)
    w = [0, -1, 0, 1] + [0] * len(P)
    w[N + P.index((2, 3))] = 1
    w[N + P.index((0, 1))] = -1
    R = {('pos', 1): Fraction(1), ('neg', 1): Fraction(-1), ('pair', 0, 1): Fraction(1)}
    print('max4 one neuron, failing cells:', len(check(N, [w], [Fraction(1)], R)))
    print('control (drop R): failing cells:', len(check(N, [w], [Fraction(1)], {})))
