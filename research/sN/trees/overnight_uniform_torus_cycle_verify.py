#!/usr/bin/env python3
"""Independent direct-residue control, without importing the cycle producer."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import time
import sympy as S


@lru_cache(None)
def step(expression, variable, center):
    return S.cancel(S.residue(expression/(variable-center),variable,center))


def main():
    started=time.monotonic()
    variables=S.symbols('x1:5')
    z=(1/S.prod(variables),)+variables
    expressions=[]
    for a in range(5):
        for c in range(5):
            if a==c:
                continue
            leaves=[i for i in range(5)if i not in(a,c)]
            g=-z[a]*S.prod(z[i]for i in leaves)*(1-z[a])
            g/=S.prod((1-z[i])*(1-z[a]*z[i])for i in leaves)
            expressions.append(S.cancel(g*S.prod(1-x for x in z)))
    rows=[]
    for tail in product((1,-1),repeat=4):
        value=0
        for expression in expressions:
            for variable,center in zip(variables,tail):
                expression=step(expression,variable,center)
            value+=6*expression
        rows.append(dict(character=(math.prod(tail),)+tail,value=str(value)))
    values=[S.Rational(row['value'])for row in rows]
    assert values==[36,36,36,36,36,36,36,36,36,36,36,36,60,60,36,84]
    result=dict(status='INDEPENDENT_ITERATED_TORUS_RESIDUE_CHECK_PASS',rows=rows,
                all_character_value=str(sum(values)),nontrivial_value=str(sum(values[1:])),
                seconds=time.monotonic()-started,
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Starts from unsimplified multiplicative G and uses direct symbolic residues. No producer import or custom Taylor-quotient recurrence.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
