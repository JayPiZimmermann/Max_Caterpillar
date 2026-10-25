#!/usr/bin/env python3
"""Exact coefficient controls for the uniform outward-star residue no-go."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import math
import sympy as S


def coefficient(k):
    p = [Q(math.comb(2*k, 2*j+1)) for j in range(k)]
    q = [Q(math.comb(2*k-1, 2*j)) for j in range(k)]
    den = [sum(p[i]*q[j-i] for i in range(j+1)) for j in range(k)]
    num = [Q((-1)**j * math.comb(4*k-3, j)) for j in range(k)]
    quotient = []
    for j in range(k):
        quotient.append((num[j]-sum(den[i]*quotient[j-i] for i in range(1,j+1)))/den[0])
    return quotient[-1]


def main():
    rows = []
    t = S.symbols('t')
    for k in range(2, 13):
        first = Q((-1)**(k-1)*math.comb(2*k-1,k-1), 2**(4*k-1))
        second = coefficient(k) / 2**(4*k-2)
        total = math.factorial(2*k)*(first+(2*k-1)*second)
        target = Q(1,2*k*2**(2*k))
        assert first * (-1)**(k-1) > 0 and second * (-1)**(k-1) > 0
        if k <= 4:
            # Independently differentiate the two closed rational functions
            # after removing their exact order-(2k-1) pole at t=1.
            a_regular = t**(2*k-1)/(1+t)**(2*k+1)
            b_regular = t**(4*k-3)/((1+t)**(2*k-1)
                          *sum(t**j for j in range(2*k))*(1+t**(2*k-1)))
            a_check = S.diff(a_regular,t,2*k-2).subs(t,1)/math.factorial(2*k-2)
            b_check = S.diff(b_regular,t,2*k-2).subs(t,1)/math.factorial(2*k-2)
            assert a_check == S.Rational(first.numerator,first.denominator)
            assert b_check == S.Rational(second.numerator,second.denominator)
        rows.append(dict(arity=2*k+1,center_mark_residue=str(first),
                         center_other_residue=str(second),full_star_orbit_residue=str(total),
                         maximum_residue=str(target)))
    assert rows[0]['full_star_orbit_residue'] == '-99/32'
    result = dict(status='EXACT_CONTROLS_FOR_UNIFORM_STAR_RESIDUE_REFUTATION',
                  rows=rows, direct_rational_derivative_controls=[5,7,9],
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='The uniform nonvanishing proof is in the companion note. This refutes only the declared first logarithmic residue, not the multiplicative deformation or the lower bound.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
