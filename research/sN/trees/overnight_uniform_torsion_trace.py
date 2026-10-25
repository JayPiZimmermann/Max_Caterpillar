#!/usr/bin/env python3
"""Exact necessary star gate for the canonical quadratic 2-torsion trace."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math

HEIGHT = (-40, 1, 3, 9, 27)


def multiply(a, b, degree):
    return [sum(a[i]*b[j-i] for i in range(j+1)) for j in range(degree+1)]


def factor(sign, power, degree):
    return [Q(int(j == 0))-Q(sign*power**j,math.factorial(j)) for j in range(degree+1)]


def star_constant(apex, center, character):
    leaves = [i for i in range(5) if i not in (apex, center)]
    poles = sum(character[apex]*character[leaf] == 1 for leaf in leaves)
    numerator = [Q(1)]+[Q(0)]*poles
    for sign, power in ((character[center],-HEIGHT[center]),
                        (character[apex],HEIGHT[apex]),
                        (character[apex],HEIGHT[apex])):
        numerator = multiply(numerator, factor(sign,power,poles), poles)
    for leaf in leaves:
        sign = character[apex]*character[leaf]
        power = HEIGHT[apex]+HEIGHT[leaf]
        assert power
        denominator = factor(sign,power,poles+1)
        if sign == 1:
            denominator = denominator[1:]
        inverse = [1/denominator[0]]
        for j in range(1,poles+1):
            inverse.append(-sum(denominator[i]*inverse[j-i] for i in range(1,j+1))/denominator[0])
        numerator = multiply(numerator,inverse,poles)
    return numerator[poles]


def main():
    levels = {}
    rows = []
    for size in (0,2,4):
        total = Q(0)
        for negative in combinations(range(5),size):
            character = tuple(-1 if i in negative else 1 for i in range(5))
            value = 6*sum(star_constant(a,c,character)
                          for a in range(5) for c in range(5) if a != c)
            total += value
            rows.append(dict(negative_labels=negative,full_star_orbit_value=str(value)))
        levels[size] = total
    gaussian = levels[0]-levels[2]+levels[4]
    nontrivial = -levels[2]+levels[4]
    assert gaussian == Q(-221057230,1356901)
    assert nontrivial == Q(-76550243,387686)
    result = dict(status='EXACT_QUADRATIC_TORSION_TRACE_STAR_REFUTATION',
                  normal=HEIGHT, constant_variable='tau; z_i=chi_i*exp(HEIGHT_i*tau)',
                  character_level_sums={str(k):str(v) for k,v in levels.items()},
                  full_gaussian_star_value=str(gaussian),full_gaussian_maximum_value=-4,
                  nontrivial_gaussian_star_value=str(nontrivial),nontrivial_gaussian_maximum_value=-5,
                  rows=rows,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Only the canonical weight (-1)^(number_of_negative_labels/2), with a uniform normalized constant coefficient. No fitted weight family was searched.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
