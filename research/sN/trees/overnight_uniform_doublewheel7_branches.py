#!/usr/bin/env python3
"""Exact witness controls for the full plus-branch types and every nondegenerate mixed-sign type."""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib
import json
import math
import time
from overnight_uniform_doublewheel7_verify import UNITS,WEIGHTS,positive_sides,add


def chart(p,q,sign):
    frequency=[(1,0,0,0,0,0)]
    next_coordinate=1
    def block(size,total):
        nonlocal next_coordinate
        running=total
        for _ in range(size-1):
            vector=tuple(int(i==next_coordinate)for i in range(6))
            next_coordinate+=1
            frequency.append(vector)
            running=tuple(x-y for x,y in zip(running,vector))
        frequency.append(running)
    block(p,(-1,0,0,0,1,0))
    block(q,(-sign,0,0,0,0,sign))
    block(6-p-q,(sign,0,0,0,-1,-sign))
    assert next_coordinate==4 and len(frequency)==7
    assert all(sum(v[i]for v in frequency)==0 for i in range(6))
    return frequency


def primitive(form):
    divisor=math.gcd(*form)
    assert divisor
    if next(v for v in form if v)<0:divisor=-divisor
    return tuple(v//divisor for v in form),divisor


def residue_tables(root,edges,frequency):
    sides=positive_sides(root,edges)
    tables=[Counter(),Counter()]
    for permutation in permutations(range(7)):
        apex=frequency[permutation[0]]
        numerator,numerator_scale=primitive(apex[:4])
        forms=[]
        for side,head in sides:
            value=apex if head else(0,)*6
            for i in side:value=add(value,frequency[permutation[i]])
            forms.extend((value,add(value,apex)))
        zero=[v for v in forms if not any(v[:4])]
        assert len(zero)<=2
        if len(zero)!=2:continue
        denominator=[];common=1
        for value in forms:
            if not any(value[:4]):continue
            form,scale=primitive(value[:4]);denominator.append(form);common*=scale
        key=(numerator,tuple(sorted(denominator)))
        for order in(0,1):
            pure=[v for v in zero if v[5-order]==0]
            if not pure:continue
            assert len(pure)==1
            other=zero[1]if zero[0]==pure[0]else zero[0]
            scale=common*pure[0][4+order]*other[5-order]
            assert scale
            tables[order][key]+=Q((-numerator_scale)**3,scale)
    return [{key:c for key,c in table.items()if c}for table in tables]


def evaluate(table,point):
    total=Q(0)
    for(numerator,denominator),coefficient in table.items():
        top=sum(x*y for x,y in zip(numerator,point))**3
        bottom=math.prod(sum(x*y for x,y in zip(factor,point))for factor in denominator)
        assert bottom
        total+=coefficient*Q(top,bottom)
    return total


def main():
    started=time.monotonic()
    rows=[]
    point=(1,10,100,1000)
    configurations=[(1,1,1),(2,1,1),(3,1,1),(2,2,1),(4,1,1),(3,2,1)]
    configurations += [(p,q,-1) for p in range(1,5) for q in range(1,6-p)]
    for p,q,sign in configurations:
        frequency=chart(p,q,sign)
        units=[residue_tables(root,edges,frequency)for root,edges in UNITS]
        for order in(0,1):
            combined=Counter()
            for weight,tables in zip(WEIGHTS,units):
                for key,c in tables[order].items():combined[key]+=weight*c
            combined={key:c for key,c in combined.items()if c}
            individual=[evaluate(tables[order],point)for tables in units]
            value=sum(w*v for w,v in zip(WEIGHTS,individual))
            assert evaluate(combined,point)==value
            row=dict(first_subset_size=p,second_subset_size=q,second_sign=sign,
                     order='s_then_t'if order==0 else't_then_s',
                     symbolic_fraction_dictionary_zero=not combined,
                     surviving_fraction_records=len(combined),
                     individual_values=list(map(str,individual)),witness_value=str(value))
            rows.append(row)
            print(json.dumps(row),'seconds',round(time.monotonic()-started,3),flush=True)
    data=dict(status='EXACT_BRANCH_WHEEL_CONTROLS_ON_THE_TWO_TERM_WITNESS',
              frequency_rule='H1=a+sum_S=s; H2=a+sign*sum_T=t; free(a,b,c,d)=(1,10,100,1000)',
              units=[dict(root=r,edges=e)for r,e in UNITS],weights=WEIGHTS,
              rows=rows,seconds=time.monotonic()-started,
              producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Dictionary-zero rows are exact rational identities. A nonzero rational evaluation proves that branch detects this witness. Zero evaluations with surviving dictionary entries alone would be inconclusive.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items()if k!='rows'},indent=2))


if __name__=='__main__':main()
