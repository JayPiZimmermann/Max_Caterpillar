#!/usr/bin/env python3
"""Recheck the boundary average through the other arithmetic parameterization.

The averaging producer uses closed-star enumeration, Cramer's rule and one
polynomial quotient.  Here use rooted cuts, Gaussian elimination and products
of Laurent inverse series from the initial gate.  The averaging producer and
its arithmetic dependency are not imported.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib
import json
import overnight_uniform_halfopen_gate as g


def main():
    terms = g.Counter()
    unit = g.family(5, 'nopath')[9]
    for p in permutations(range(5)):
        terms.update(g.basis_expansion(unit, p))
    terms = {basis: c for basis, c in terms.items() if c}
    star = target = Q(0)
    for p in permutations((0, 1, 10, 100, 1000)):
        g.ETA = tuple(x - p[0] for x in p[1:])
        g.lifted_constant.cache_clear()
        star += sum(c * g.lifted_constant(basis) for basis, c in terms.items())
        target += g.lifted_constant(tuple(g.coordinate(i) for i in range(1, 5)))
    assert star / 120 == Q(-368789, 151200)
    assert target / 120 == Q(1, 80)
    result = dict(status='INDEPENDENT_ARITHMETIC_PARAMETERIZATION_PASS',
                  star_average=str(star / 120), maximum_average=str(target / 120),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Rooted-cut/Gaussian/product-Laurent replay, independent of the averaging producer closed-star/Cramer/single-quotient route. Not independent of the initial unsymmetrized gate.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
