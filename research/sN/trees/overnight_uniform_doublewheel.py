#!/usr/bin/env python3
"""Exact N5 outward-twin double-wheel injectivity and local-arrangement gate."""
from itertools import combinations,permutations
from pathlib import Path
import hashlib
import json
import math
import sympy as S
from dfs_review_fourier import family


def arrangement_control(n):
    allowed={(1,0),(0,1),(1,1),(1,-1)}
    count=0
    for apex in range(n):
        others=[i for i in range(n)if i!=apex]
        for size in range(1,n-1):
            for subset in combinations(others,size):
                for shift in (0,1,-1):
                    form=[int(i in subset)+shift*int(i==apex)for i in range(n)]
                    if len(set(form[3:]))!=1:
                        continue
                    offset=form[3]
                    x,y=form[1]-offset,form[2]-offset
                    if form[0]-offset!=x+y or not(x or y):
                        continue
                    divisor=math.gcd(x,y)
                    x,y=x//divisor,y//divisor
                    if x<0 or(x==0 and y<0):x,y=-x,-y
                    assert(x,y)in allowed
                    if apex>=3:assert(x,y)in{(1,0),(0,1)}
                    count+=1
    return dict(labels=n,localized_forms=count,only_B2_lines=True,
                outside_apex_only_two_wheel_lines=True)


def main():
    a,b=S.symbols('a b')
    frequencies=((1,0,0,0),(-1,0,1,0),(-1,0,0,1),(0,1,0,0),(1,-1,-1,-1))
    def add(x,y,scale=1):return tuple(v+scale*w for v,w in zip(x,y))
    units=family(5,'nopath')
    rows=[]
    for index in (0,3,6,9):
        unit=units[index]
        total=0
        two_pole_terms=0
        for p in permutations(range(5)):
            apex=frequencies[p[0]]
            factors=[]
            for side,sign in unit['cuts']:
                cut=(0,0,0,0)
                for vertex in side:cut=add(cut,frequencies[p[vertex]])
                factors.extend((cut,add(cut,apex,sign)))
            zero=[f for f in factors if f[:2]==(0,0)]
            assert len(zero)<=2
            if len(zero)!=2:continue
            assert p[0]in(0,1,2)
            two_pole_terms+=1
            pure=[f for f in zero if f[3]==0]
            if not pure:continue
            assert len(pure)==1
            other=zero[1]if zero[0]==pure[0]else zero[0]
            denominator=pure[0][2]*other[3]*S.prod(f[0]*a+f[1]*b for f in factors if f[:2]!=(0,0))
            total-= (apex[0]*a+apex[1]*b)/denominator
        rows.append(dict(index=index,unit=unit,two_pole_terms=two_pole_terms,
                         residue=str(S.factor(total))))
    functions=[S.sympify(row['residue'])for row in rows]
    assert S.cancel(functions[0]-functions[3])==0
    denominator=S.lcm([S.denom(S.cancel(f))for f in functions[:3]])
    polynomials=[S.Poly(S.cancel(denominator*f),a,b)for f in functions[:3]]
    monomials=sorted({m for p in polynomials for m,c in p.terms()})
    matrix=S.Matrix([[p.coeff_monomial(m)for p in polynomials]for m in monomials])
    assert matrix.rank()==3
    result=dict(status='EXACT_N5_SYMMETRIC_OUTWARD_TWIN_DOUBLEWHEEL_INJECTIVITY',
                frequency_chart='(a,s-a,t-a,b,a-b-s-t)',residue_order=['s','t'],
                rows=rows,common_denominator=str(denominator),
                coefficient_monomials=monomials,coefficient_matrix=[list(map(int,row))for row in matrix.tolist()],
                rank=3,arrangement_controls=[arrangement_control(n)for n in range(5,10)],
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Exact injectivity on the symmetric N5 outward-twin span only. Uniform injectivity is not proved; the arrangement lemma is proved separately.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
