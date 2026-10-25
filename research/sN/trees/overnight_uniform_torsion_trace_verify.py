#!/usr/bin/env python3
"""Independent star gate via original G, t-1 series, and dt/(t log t)."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math

HEIGHT = (-40,1,3,9,27)


def choose(n,k):
    return Q(math.prod(n-j for j in range(k)),math.factorial(k))


def multiply(a,b,degree):
    out=[Q(0)]*(degree+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=degree:
                out[i+j]+=x*y
    return out


def factor(sign,power,degree):
    return [Q(int(j==0))-sign*choose(power,j) for j in range(degree+1)]


def constant(apex,center,chi):
    leaves=[i for i in range(5) if i not in (apex,center)]
    den_factors=[(chi[l],HEIGHT[l]) for l in leaves]
    den_factors += [(chi[apex]*chi[l],HEIGHT[apex]+HEIGHT[l]) for l in leaves]
    poles=sum(sign==1 for sign,power in den_factors)
    sign=-chi[apex]*math.prod(chi[l] for l in leaves)
    power=HEIGHT[apex]+sum(HEIGHT[l] for l in leaves)
    numerator=[sign*choose(power,j) for j in range(poles+1)]
    # Original G numerator times all five normalization factors.
    for i in [apex]+list(range(5)):
        numerator=multiply(numerator,factor(chi[i],HEIGHT[i],poles),poles)
    denominator=[Q(1)]+[Q(0)]*poles
    for sign,power in den_factors:
        values=factor(sign,power,poles+1)
        if sign==1:
            values=values[1:]
        denominator=multiply(denominator,values[:poles+1],poles)
    quotient=[]
    for j in range(poles+1):
        quotient.append((numerator[j]-sum(denominator[i]*quotient[j-i] for i in range(1,j+1)))/denominator[0])
    def coefficient(exponent):
        index=poles+exponent
        return quotient[index] if index>=0 else Q(0)
    assert all(coefficient(j)==0 for j in range(-poles,-2))
    assert coefficient(-1)==coefficient(-2) # reciprocity under t -> 1/t
    # Res f(t)dt/(t log t), with 1/(t log t)=1/(t-1)-1/2+5(t-1)/12+...
    return coefficient(0)-coefficient(-1)/2+Q(5,12)*coefficient(-2)


def main():
    levels={}
    for size in (0,2,4):
        total=Q(0)
        for negative in combinations(range(5),size):
            chi=tuple(-1 if i in negative else 1 for i in range(5))
            total+=6*sum(constant(a,c,chi)for a in range(5)for c in range(5)if a!=c)
        levels[size]=total
    assert levels == {0:Q(7210557,208754),2:Q(519060327,1356901),4:Q(502268953,2713802)}
    result=dict(status='INDEPENDENT_QUADRATIC_TORSION_TRACE_CHECK_PASS',
                character_level_sums={str(k):str(v)for k,v in levels.items()},
                gaussian_value=str(levels[0]-levels[2]+levels[4]),
                nontrivial_value=str(-levels[2]+levels[4]),
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='No producer import. Uses the unsimplified multiplicative kernel, binomial t-1 expansion, and logarithmic residue conversion rather than exponential series of the simplified star fraction.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
