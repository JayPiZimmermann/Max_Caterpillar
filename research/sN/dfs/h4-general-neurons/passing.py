"""Exact 3-locality passing test for general neurons (model A, translation invariant).

Neuron data: symmetric weights a[(i,j)] (i<j) of |x_i-x_j| and vertex values kappa[v],
with sum(kappa) = sum(a).  Then g = <l,x> + sum a_ij |x_i-x_j|, l_v = 2 kappa_v - A_v.

3-locality L = (T, order of O from top to bottom).  With generic heights,
g(p_L) = 0 iff for each o in O: sum_{j in T or above o} a_oj = kappa_o   (E_L).
Germ at T: h(z) = sum_t s_t z_t + sum_{i<j in T} a_ij |z_i-z_j|, s_t = 2 kappa_t - sum_{j in T} a_tj.
relu(h) is NOT a sum of functions of two coordinates (=> passes) iff
  (i) h has a sign change strictly inside one of the six braid sectors, or
  (ii) the braid-ray values of relu(h) violate the single linear relation satisfied
       by span{relu(z_i-z_j), z_i} (invariant lam).
All arithmetic exact (Fraction).
"""
from fractions import Fraction as Fr
import itertools

# rays in plane z_c = 0, coordinates (z_a, z_b, z_c), sorted by angle in (u,v)=(z_a,z_b)
RAYS = [(1, 0, 0), (1, 1, 0), (0, 1, 0), (-1, 0, 0), (-1, -1, 0), (0, -1, 0)]


def _span_funcs():
    r = lambda t: max(t, 0)
    fs = [lambda z: r(z[0] - z[1]), lambda z: r(z[0] - z[2]), lambda z: r(z[1] - z[2]),
          lambda z: z[0] - z[2], lambda z: z[1] - z[2]]
    return [[Fr(f(z)) for f in fs] for z in RAYS]


def _left_null():
    import sympy
    M = sympy.Matrix(_span_funcs())  # 6 x 5
    ns = M.T.nullspace()
    assert len(ns) == 1
    v = ns[0]
    return [Fr(int(sympy.fraction(x)[0]), int(sympy.fraction(x)[1])) for x in v]


LAM = _left_null()


def h_val(s, aT, z):
    # s: slopes (3), aT: dict over pairs (0,1),(0,2),(1,2) of local indices
    v = sum(Fr(si) * zi for si, zi in zip(s, z))
    for (i, j), w in aT.items():
        v += Fr(w) * abs(z[i] - z[j])
    return v


def germ_passes(s, aT):
    hv = [h_val(s, aT, z) for z in RAYS]
    for k in range(6):
        x, y = hv[k], hv[(k + 1) % 6]
        if (x > 0 and y < 0) or (x < 0 and y > 0):
            return True
    fv = [max(x, Fr(0)) for x in hv]
    return sum(l * f for l, f in zip(LAM, fv)) != 0


def localities(N):
    for T in itertools.combinations(range(N), 3):
        O = [v for v in range(N) if v not in T]
        for order in itertools.permutations(O):
            yield T, order


def A(a, i, j):
    if i == j:
        return 0
    return a.get((min(i, j), max(i, j)), 0)


def equations_hold(a, kappa, T, order):
    above = list(T)
    for o in order:
        if sum(A(a, o, j) for j in above) != kappa[o]:
            return False
        above.append(o)
    return True


def germ(a, kappa, T):
    s = [2 * Fr(kappa[t]) - sum(Fr(A(a, t, u)) for u in T) for t in T]
    aT = {(0, 1): A(a, T[0], T[1]), (0, 2): A(a, T[0], T[2]), (1, 2): A(a, T[1], T[2])}
    return s, aT


def passes(a, kappa, T, order):
    if not equations_hold(a, kappa, T, order):
        return False
    s, aT = germ(a, kappa, T)
    return germ_passes(s, aT)


def count_passing(N, a, kappa):
    assert sum(Fr(v) for v in kappa) == sum(Fr(v) for v in a.values())
    return sum(1 for T, o in localities(N) if passes(a, kappa, T, o))


if __name__ == '__main__':
    # self-tests: max_3 germ passes; relu(z_a - z_b) does not; ridge z_a+z_b-2z_c passes
    print('LAM', LAM)
    # relu(h) with h = max(z_a,z_b) - z_c = (z_a+z_b)/2 + |z_a-z_b|/2 - z_c
    print('max-type', germ_passes([Fr(1, 2), Fr(1, 2), -1], {(0, 1): Fr(1, 2)}))
    print('hinge', germ_passes([1, -1, 0], {}))
    print('ridge', germ_passes([1, 1, -2], {}))
    print('abs', germ_passes([0, 0, 0], {(0, 1): 1}))
    # N=4 neuron g = max(x0,x1) - max(x2,x3): a01 = 1/2, a23 = -1/2, l = (1/2,1/2,-1/2,-1/2)
    # kappa_v = (l_v + A_v)/2
    a = {(0, 1): Fr(1, 2), (2, 3): Fr(-1, 2)}
    l = [Fr(1, 2), Fr(1, 2), Fr(-1, 2), Fr(-1, 2)]
    Av = [Fr(1, 2), Fr(1, 2), Fr(-1, 2), Fr(-1, 2)]
    kappa = [(l[v] + Av[v]) / 2 for v in range(4)]
    print('N=4 double max neuron passes', count_passing(4, a, kappa), 'of', 4)
