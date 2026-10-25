#!/usr/bin/env python3
"""Exact chamber-span test for bounded fan extensions of the known max5 atoms.

Full permutation sums give a necessary control, not an exponential all-N
construction. A positive passes the complete integer kink/linear system.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations,product
from pathlib import Path
import hashlib,json,math,sys,time

import numpy as np
from flint import nmod_mat,ctx
from exponential_families_probe import ratrec

HERE=Path(__file__).parent
SOURCE=HERE.parent/'best5/overnight_fixed_cross_net9_17.json'
P=1000000007
ctx.threads=1


def normalized(vector):
    common=math.lcm(*(x.denominator for x in vector));values=[int(x*common) for x in vector]
    divisor=math.gcd(*values)
    if not divisor:return tuple(values)
    if next(x for x in values if x)<0:divisor=-divisor
    return tuple(x//divisor for x in values)


def main(n):
    assert n in (5,6);started=time.monotonic();source=json.loads(SOURCE.read_text())
    features=[tuple(row) for row in source['first_layer'][:7]]
    templates={normalized(list(map(Q,row[:7]))) for row in source['second_layer'][2:]}
    assert all(not any(Q(x) for x in row[7:]) for row in source['second_layer'][2:])
    if n==6:
        features=[v+(0,) for v in features]
        features += [(-1,0,0,0,0,1),(0,0,0,-1,0,1)]
        candidates=sorted({normalized([Q(x) for x in v]+[Q(a),Q(b)]) for v in templates for a,b in product(range(-2,3),repeat=2)})
    else:candidates=sorted(templates)
    profiles=[]
    for pi in permutations(range(n)):
        position={v:i for i,v in enumerate(pi)};forms=[]
        for feature in features:
            positive=next(i for i,x in enumerate(feature) if x==1);negative=next(i for i,x in enumerate(feature) if x==-1)
            forms.append([int(position[positive]<=j<position[negative]) for j in range(n-1)])
        profiles.append(forms)
    profiles=np.asarray(profiles,dtype=np.int32)
    columns=[];all_kinks=set()
    for vector in candidates:
        values=np.einsum('ijk,j->ik',profiles,np.asarray(vector,dtype=np.int32));kinks=defaultdict(int);linear=[0]*(n-1)
        for raw in values:
            a=tuple(map(int,raw))
            if min(a)>=0:
                linear=[x+y for x,y in zip(linear,a)];continue
            if max(a)<=0:continue
            divisor=math.gcd(*a);sign=1 if next(x for x in a if x)>0 else -1
            key=tuple(x//(sign*divisor) for x in a);kinks[key]+=divisor
            if sign<0:linear=[x+y for x,y in zip(linear,a)]
        columns.append((dict(kinks),linear));all_kinks.update(kinks)
    kink_order=sorted(all_kinks);rows=[]
    for kink in kink_order:rows.append([col[0].get(kink,0) for col in columns]+[0,0])
    for j in range(n-1):rows.append([col[1][j] for col in columns]+[(j+1)*(n-j-1),n-j-1])
    print('FAMILY',n,len(candidates),'CONSTRAINTS',len(rows),'KINKS',len(kink_order),'SECONDS',time.monotonic()-started,flush=True)
    rr,rank=nmod_mat(rows,P).rref();width=len(candidates)+1;pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)]
    target=width in pivots
    result=dict(status='MODULAR_CHAMBER_SPAN_DIAGNOSTIC',n=n,prime=P,features=features,candidates=candidates,
                normalized_templates=sorted(templates),permutations=math.factorial(n),kink_normals=kink_order,
                integer_rows=rows,ranks=[rank-int(target),rank],source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started,
                scope='S_N symmetrized bounded fan atoms plus a pairwise-absolute-value auxiliary; exact chamber equations, not Fourier samples.')
    if not target:
        coefficients=[Q(0)]*width
        for i,pivot in enumerate(pivots):coefficients[pivot]=ratrec(int(rr[i,width]),P)
        if all(c is not None for c in coefficients):
            assert all(sum(c*x for c,x in zip(coefficients,row[:-1]))==row[-1] for row in rows)
            result.update(status='EXACT_SYMMETRIC_FAN_IDENTITY',coefficients=list(map(str,coefficients)))
    elif rank==width+1:result['status']='EXACT_FULL_COLUMN_CHAMBER_OBSTRUCTION'
    path=HERE/f'overnight_upper_fan_lift_{n}.json';path.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('DONE',result['status'],'RANKS',result['ranks'],'SECONDS',result['seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]))
