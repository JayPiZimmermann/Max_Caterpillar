#!/usr/bin/env python3
"""Bounded exact N5 constant-coefficient gate for the half-open OS lift."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import hashlib
import json
import time
from dfs_review_fourier import family

N = 5
RANK = N - 1
ETA = (1, 10, 100, 1000)
HEIGHT = (1, 3, 9, 27)


def add(a, b, scale=1):
    return tuple(x + scale * y for x, y in zip(a, b))


def coordinate(i):
    return (-1,) * RANK if i == 0 else tuple(int(j == i - 1) for j in range(RANK))


@lru_cache(None)
def solve(basis, vector):
    a = [[Q(basis[j][i]) for j in range(RANK)] + [Q(vector[i])]
         for i in range(RANK)]
    det = Q(1)
    for i in range(RANK):
        pivot = next(j for j in range(i, RANK) if a[j][i])
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            det = -det
        value = a[i][i]
        det *= value
        a[i] = [x / value for x in a[i]]
        for j in range(RANK):
            if j != i:
                value = a[j][i]
                a[j] = [x - value * y for x, y in zip(a[j], a[i])]
    assert abs(det) == 1, ('nonunimodular canonical basis', basis, det)
    return tuple(row[-1] for row in a)


def binomial_integer(n, k):
    value = Q(1)
    for j in range(k):
        value *= Q(n - j, j + 1)
    return value


def convolution(a, b, degree):
    return [sum(a[i] * b[k - i] for i in range(k + 1))
            for k in range(degree + 1)]


@lru_cache(None)
def lifted_constant(basis):
    coefficients = solve(basis, ETA)
    assert all(coefficients), ('nongeneric eta', basis, coefficients)
    numerator = (0,) * RANK
    for ray, coefficient in zip(basis, coefficients):
        if coefficient < 0:
            numerator = add(numerator, ray)
    numerator_sign = (-1) ** (sum(numerator) % 2)
    numerator_height = sum(x * y for x, y in zip(numerator, HEIGHT))
    factors = []
    poles = 0
    for ray in basis:
        sign = (-1) ** (sum(ray) % 2)
        height = sum(x * y for x, y in zip(ray, HEIGHT))
        assert height, ('nongeneric perturbation', ray)
        denominator = [Q(int(k == 0)) - sign * binomial_integer(height, k)
                       for k in range(RANK + 2)]
        pole = int(sign == 1)
        poles += pole
        denominator = denominator[pole:]
        inverse = [1 / denominator[0]]
        for k in range(1, RANK + 1):
            inverse.append(-sum(denominator[j] * inverse[k - j]
                                for j in range(1, k + 1)) / denominator[0])
        factors.append(inverse)
    series = [numerator_sign * binomial_integer(numerator_height, k)
              for k in range(RANK + 1)]
    for factor in factors:
        series = convolution(series, factor, RANK)
    return series[poles]


def basis_expansion(unit, permutation):
    apex = coordinate(permutation[0])
    cuts = []
    signs = []
    for side, sign in unit['cuts']:
        cut = (0,) * RANK
        for vertex in side:
            cut = add(cut, coordinate(permutation[vertex]))
        cuts.append(cut)
        signs.append(sign)
    d = len(cuts)
    marker_coefficients = solve((apex,) + tuple(cuts), coordinate(0))
    terms = Counter()
    for selected in range(d + 1):
        multiplier = marker_coefficients[selected]
        if not multiplier:
            continue
        free = [e for e in range(d) if selected == 0 or e != selected - 1]
        sign_product = (-1) ** (d - 2)
        for e in free:
            sign_product *= signs[e]
        for bits in product((0, 1), repeat=len(free)):
            chosen = dict(zip(free, bits))
            if selected:
                chosen[selected - 1] = 1
            basis = [apex] + [add(cuts[e], apex, chosen[e] * signs[e]) for e in range(d)]
            terms[tuple(sorted(basis))] += multiplier * sign_product * (-1) ** sum(bits)
    return terms


def main():
    started = time.monotonic()
    units = family(N, 'nopath')
    rows = []
    for index, unit in enumerate(units):
        terms = Counter()
        for permutation in permutations(range(N)):
            terms.update(basis_expansion(unit, permutation))
        terms = {basis: value for basis, value in terms.items() if value}
        value = sum(coefficient * lifted_constant(basis) for basis, coefficient in terms.items())
        literal_outtwins = any(sum(1 for leaf, hub in unit['edges']
                                   if hub == candidate and leaf != unit['root']
                                   and sum(leaf in e for e in unit['edges']) == 1) >= 2
                               for candidate in range(1, N))
        record = dict(index=index, unit=unit, basis_terms=len(terms),
                      literal_outward_twins=literal_outtwins, value=str(value))
        rows.append(record)
        print(json.dumps(record), flush=True)
    target_basis = tuple(coordinate(i) for i in range(1, N))
    target = lifted_constant(target_basis)
    assert target == Q(1, 16)
    data = dict(status='EXACT_N5_HALFOPEN_TORSION_CONSTANT_GATE', eta=ETA, height=HEIGHT,
                torsion_signs=[1, -1, -1, -1, -1], marker=0,
                parameter='z_i=sign_i*(1+s)^height_i; height_0=-40',
                full_orbit_star_rows=rows, unsymmetrized_maximum_value=str(target),
                literal_outtwin_annihilation=all(Q(row['value']) == 0 for row in rows if row['literal_outward_twins']),
                cached_basis_constants=lifted_constant.cache_info().currsize,
                seconds=time.monotonic() - started,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Exact scalar constant coefficient of a proved linear half-open-cone lift. No uniform separator claim.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data), flush=True)


if __name__ == '__main__':
    main()
