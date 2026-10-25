#!/usr/bin/env python3
"""One exact N5 iterated local-cycle gate with explicit test poles."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import time
import sympy as S

Z = S.symbols('z1:5')


@lru_cache(None)
def constant(expression, variable, center):
    if expression == 0:
        return S.Integer(0)
    numerator, denominator = S.fraction(S.cancel(expression))
    pole = 0
    while S.expand(denominator.subs(variable,center)) == 0:
        quotient, remainder = S.div(denominator,variable-center,variable)
        assert S.expand(remainder) == 0
        denominator = quotient
        pole += 1
    n = [S.diff(numerator,variable,j).subs(variable,center)/math.factorial(j)
         for j in range(pole+1)]
    d = [S.diff(denominator,variable,j).subs(variable,center)/math.factorial(j)
         for j in range(pole+1)]
    out = []
    for j in range(pole+1):
        out.append(S.cancel((n[j]-sum(d[i]*out[j-i]for i in range(1,j+1)))/d[0]))
    return out[pole]


def main():
    start=time.monotonic()
    z=(1/S.prod(Z),)+Z
    terms=[]
    for apex in range(5):
        for center in range(5):
            if apex==center:
                continue
            leaves=[i for i in range(5)if i not in(apex,center)]
            terms.append(S.cancel((1-1/z[center])*(1-z[apex])**2
                                  /S.prod(1-z[apex]*z[i]for i in leaves)))
    rows=[]
    for tail in product((1,-1),repeat=4):
        character=(math.prod(tail),)+tail
        value=0
        for expression in terms:
            for variable,center in zip(Z,tail):
                expression=constant(expression,variable,center)
            assert expression.is_Rational
            value+=6*expression
        row=dict(character=character,full_star_orbit_value=str(value),maximum_value=1)
        rows.append(row)
        print(json.dumps(row),'seconds',round(time.monotonic()-start,3),flush=True)
    all_value=sum(S.Rational(row['full_star_orbit_value'])for row in rows)
    nontrivial=sum(S.Rational(row['full_star_orbit_value'])for row in rows
                  if any(x<0 for x in row['character']))
    data=dict(status='EXACT_N5_ITERATED_TORUS_CYCLE_GATE',
              coordinate_order=[str(z)for z in Z],rows=rows,
              all_character_star_value=str(all_value),all_character_maximum_value=16,
              nontrivial_character_star_value=str(nontrivial),nontrivial_character_maximum_value=15,
              seconds=time.monotonic()-start,
              producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Iterated residues F(z)*product_i dz_i/(z_i-chi_i), with z0=(z1*z2*z3*z4)^-1. All wheel/test-pole collisions include their derivative residues. One fixed coordinate order and uniform character sums only.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items()if k!='rows'},indent=2))


if __name__=='__main__':
    main()
