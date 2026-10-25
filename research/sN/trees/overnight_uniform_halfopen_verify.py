#!/usr/bin/env python3
"""Independent stdlib outward-star check; no producer imports.

Uses the closed star formula, Cramer's rule, and a single polynomial quotient
after removing all powers of t-1.  This differs from the producer's rooted
cut inventory, Gaussian solver, and product of Laurent inverse series.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import hashlib
import json
import math

ETA = (1, 10, 100, 1000)
HEIGHT = (1, 3, 9, 27)


def vertex(i):
    return (-1,) * 4 if i == 0 else tuple(int(j + 1 == i) for j in range(4))


def determinant(columns):
    value = 0
    for p in permutations(range(4)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(4) for j in range(i + 1, 4))
        value += sign * math.prod(columns[j][p[j]] for j in range(4))
    return value


def choose(n, k):
    return Q(math.prod(n - j for j in range(k)), math.factorial(k))


def multiply(a, b, degree):
    result = [Q(0)] * (degree + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= degree:
                result[i + j] += x * y
    return result


def constant(basis, eta=ETA):
    det = determinant(basis)
    assert abs(det) == 1
    offset = [0] * 4
    for j in range(4):
        replaced = list(basis)
        replaced[j] = eta
        coefficient = Q(determinant(replaced), det)
        assert coefficient
        if coefficient < 0:
            offset = [a + b for a, b in zip(offset, basis[j])]
    numerator_sign = (-1) ** (sum(offset) % 2)
    exponent = sum(a * b for a, b in zip(offset, HEIGHT))
    poles = sum(sum(ray) % 2 == 0 for ray in basis)
    denominator = [Q(1)] + [Q(0)] * poles
    for ray in basis:
        height = sum(a * b for a, b in zip(ray, HEIGHT))
        sign = (-1) ** (sum(ray) % 2)
        assert height
        power = abs(height)
        if height < 0:
            exponent += power
        if sign == 1:
            # (1-t^h)/(t-1) = -sum t^j for h>0;
            # for h<0 its numerator is +sum t^j after clearing t^-h.
            if height > 0:
                numerator_sign = -numerator_sign
            factor = [sum(choose(j, k) for j in range(power)) for k in range(poles + 1)]
        else:
            factor = [Q(int(k == 0)) + choose(power, k) for k in range(poles + 1)]
        denominator = multiply(denominator, factor, poles)
    numerator = [numerator_sign * choose(exponent, k) for k in range(poles + 1)]
    quotient = []
    for k in range(poles + 1):
        quotient.append((numerator[k] - sum(denominator[j] * quotient[k - j]
                                             for j in range(1, k + 1))) / denominator[0])
    return quotient[poles]


def direct_star_terms():
    terms = Counter()
    # Six leaf permutations give the same rooted star for each apex/center.
    for apex in range(5):
        for center in range(5):
            if apex == center:
                continue
            leaves = [i for i in range(5) if i not in (apex, center)]
            # R=-a/product_l l(l+a).  The marker is omega_0.
            if apex == 0:
                components = [('a', 1)]
            elif center == 0:
                components = [('a', -1)] + [(leaf, -1) for leaf in leaves]
            else:
                components = [(0, 1)]
            for selected, coefficient in components:
                free = leaves if selected == 'a' else [leaf for leaf in leaves if leaf != selected]
                for bits in product((0, 1), repeat=len(free)):
                    assignment = dict(zip(free, bits))
                    if selected != 'a':
                        assignment[selected] = 1
                    rays = [vertex(apex)]
                    for leaf in leaves:
                        rays.append(tuple(x + assignment[leaf] * y
                                          for x, y in zip(vertex(leaf), vertex(apex))))
                    terms[tuple(sorted(rays))] += -6 * coefficient * (-1) ** sum(bits)
    return {basis: coefficient for basis, coefficient in terms.items() if coefficient}


def main():
    terms = direct_star_terms()
    value = sum(coefficient * constant(basis) for basis, coefficient in terms.items())
    target = constant(tuple(vertex(i) for i in range(1, 5)))
    assert len(terms) == 97
    assert value == Q(-57047, 3360)
    assert target == Q(1, 16)
    # Explicit rank-two OS circuit with eta=(1,10):
    # 1/((1-X)(1-Y)) = X/((1-X)(1-XY)) + 1/((1-Y)(1-XY)).
    left_numerator = {(0, 0): 1, (1, 1): -1}
    right_numerator = Counter({(1, 0): 1, (1, 1): -1})
    right_numerator.update({(0, 0): 1, (1, 0): -1})
    assert {k: v for k, v in right_numerator.items() if v} == left_numerator
    result = dict(status='INDEPENDENT_EXACT_HALFOPEN_CONSTANT_REFUTATION',
                  outward_star_full_orbit_value=str(value), maximum_value=str(target),
                  surviving_basis_terms=len(terms), rank_two_complete_circuit_checked=True,
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='The selected torsion constant fails already for the outward star. The half-open lift itself respects full circuit relations by the separate cone-valuation proof.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
