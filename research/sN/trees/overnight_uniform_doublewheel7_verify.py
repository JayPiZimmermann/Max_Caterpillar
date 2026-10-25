#!/usr/bin/env python3
"""Independent exact two-term refutation of leaf-double-wheel injectivity.

No producer imports or proposed residue rows. Positive-endpoint components,
a different external-frequency basis, all5040permutations, literal fraction
coefficient cancellation, and a fresh exact nonzero Fourier evaluation.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib
import json
import math
import time

UNITS=[(1,((1,2),(1,3),(1,4),(5,2),(6,2))),
       (1,((1,2),(1,3),(4,2),(5,2),(6,2)))]
WEIGHTS=(-3,2)


def positive_sides(root,edges):
    adjacency={v:[]for v in range(1,7)}
    for x,y in edges:adjacency[x].append(y);adjacency[y].append(x)
    sides=[]
    for x,y in edges:
        side={x};queue=[x]
        while queue:
            v=queue.pop()
            for w in adjacency[v]:
                if {v,w}=={x,y}or w in side:continue
                side.add(w);queue.append(w)
        sides.append((tuple(sorted(side)),int(root in side)))
    return sides


def add(a,b):return tuple(x+y for x,y in zip(a,b))


def fractions(root,edges):
    # (a,s-a,t-a,b,c,d,a-b-c-d-s-t), unlike the producer's four outside variables.
    frequency=((1,0,0,0,0,0),(-1,0,0,0,1,0),(-1,0,0,0,0,1),
               (0,1,0,0,0,0),(0,0,1,0,0,0),(0,0,0,1,0,0),(1,-1,-1,-1,-1,-1))
    sides=positive_sides(root,edges)
    result=Counter();outside=0
    for permutation in permutations(range(7)):
        apex=frequency[permutation[0]]
        forms=[]
        for side,contains_root in sides:
            q=apex if contains_root else (0,)*6
            for vertex in side:q=add(q,frequency[permutation[vertex]])
            forms.extend((q,add(q,apex)))
        zero=[form for form in forms if not any(form[:4])]
        assert len(zero)<=2
        if permutation[0]>=3:
            assert len(zero)<2
            outside+=1
        if len(zero)!=2:continue
        pure=[form for form in zero if form[5]==0]
        if not pure:continue
        assert len(pure)==1
        other=zero[1]if zero[0]==pure[0]else zero[0]
        scale=pure[0][4]*other[5]
        key=[]
        for form in forms:
            if not any(form[:4]):continue
            divisor=math.gcd(*form[:4])
            if next(x for x in form[:4]if x)<0:divisor=-divisor
            key.append(tuple(x//divisor for x in form[:4]));scale*=divisor
        assert len(key)==8
        result[tuple(sorted(key))]+=Q(-1 if permutation[0]==0 else 1,scale)
    return {key:value for key,value in result.items()if value},outside


def exact_value(root,edges,point):
    sides=positive_sides(root,edges)
    value=Q(0)
    for omega in permutations(point):
        denominator=1
        for side,contains_root in sides:
            q=sum(omega[i]for i in side)+contains_root*omega[0]
            denominator*=q*(q+omega[0])
        assert denominator
        value+=Q((-omega[0])**3,denominator)
    return value


def main():
    started=time.monotonic()
    tables=[];outside=[]
    for root,edges in UNITS:
        table,count=fractions(root,edges);tables.append(table);outside.append(count)
    assert outside==[2880,2880]
    union=set(tables[0])|set(tables[1])
    assert all(sum(w*table.get(key,0)for w,table in zip(WEIGHTS,tables))==0 for key in union)
    point=(-33,3,4,5,6,7,8)
    values=[exact_value(root,edges,point)for root,edges in UNITS]
    witness=sum(w*v for w,v in zip(WEIGHTS,values))
    assert witness==Q(1023022803722705038478750493973,455746540313582618712131520000000)
    result=dict(status='EXACT_NONZERO_OUTWARD_TWIN_FUNCTION_WITH_ZERO_LEAF_DOUBLEWHEELS',
                units=[dict(root=r,apex=0,edges=e)for r,e in UNITS],weights=WEIGHTS,
                orbit_convention='Unaveraged fullS7 sums; every labelled permutation included.',
                residue_chart='(a,s-a,t-a,b,c,d,a-b-c-d-s-t)',
                fraction_counts=[len(t)for t in tables],common_fraction_count=len(union),
                every_fraction_coefficient_cancels=True,outside_apex_terms_checked=outside,
                nonzero_point=point,individual_values=list(map(str,values)),nonzero_value=str(witness),
                fraction_coefficients=[dict(denominator=key,coefficients=[str(table.get(key,0))for table in tables])for key in sorted(union)],
                seconds=time.monotonic()-started,
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Refutes injectivity of the complete leaf-double-wheel leading map on the symmetric outward-twin span atN7. Does not put the maximum in that span or refute outward-twin separation.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='fraction_coefficients'},indent=2))


if __name__=='__main__':main()
