#!/usr/bin/env python3
"""Exact Fourier gate for the fixed-support multi-prime proposal.

The compact engine is decoded into canonical rational-function terms. Its
normalization is controlled against the separate general-head expression
constructor before the unchanged symbolic principal-parts checker is invoked.
"""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import random
import struct
import sys
import time

import numpy as np
import overnight_upper_probe as base
from exponential_families_probe import exact_expression
from rational_identity import Verifier

HERE=Path(__file__).parent
CRT=HERE/'overnight_upper_modular_multicrt.json'
ENGINE=HERE/'overnight_upper_modular_engine.bin'
FAMILY=HERE/'overnight_upper_modular_bfs_7_family.json'


def decode():
    with ENGINE.open('rb') as f:
        magic,n,nf,npairs,nu,nc=struct.unpack('<6Q',f.read(48));assert magic==0x5550504552504149
        forms=np.fromfile(f,dtype='<i4',count=nf*n).reshape(nf,n)
        pairs=np.fromfile(f,dtype='<u4',count=npairs*2).reshape(npairs,2)
        incidence=np.fromfile(f,dtype='<u4',count=nu*(n-2)).reshape(nu,n-2)
        apices=np.fromfile(f,dtype='u1',count=nu)
        offsets=np.fromfile(f,dtype='<u8',count=nc+1)
        assert not f.read(1) and offsets[-1]==nu
    canonical=[];scales=[]
    for form in forms:
        reduced=tuple(int(x)-int(form[-1]) for x in form[:-1])+(0,)
        gcd=math.gcd(*reduced)
        if next(x for x in reduced if x)<0:gcd=-gcd
        canonical.append(tuple(x//gcd for x in reduced));scales.append(gcd)
    numerators=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(1,)*(n-1)+(0,)]
    one=(0,)*(n-1)+(1,)

    def unit(index):
        apex=int(apices[index]);num=numerators[apex];power=n-4
        scale=Q((-1)**power if apex<n-1 else 1);den=Counter()
        for pair in incidence[index]:
            for idx in pairs[pair]:den[canonical[idx]]+=1;scale/=scales[idx]
        cancel=min(power,den[num]);power-=cancel;den[num]-=cancel
        return (num if power else one,power,tuple(sorted((form,mult) for form,mult in den.items() if mult))),scale

    return int(n),offsets,unit


def build(data,controls=True):
    n,offsets,unit=decode();selected=data['selected_columns'];coefficients=list(map(Q,data['coefficients']))
    result=defaultdict(Q);checked=0
    if controls:
        family=json.loads(FAMILY.read_text())['orbits'];rng=random.Random(2510251)
        for col in rng.sample(selected,min(16,len(selected))):
            index=int(offsets[col]);key,scale=unit(index)
            direct=exact_expression(n,[[family[col][0]]],[Q(1)])
            target=exact_expression(n,[],[])
            for term,c in target.items():direct[term]-=c
            assert {k:v for k,v in direct.items() if v}=={key:scale}
            checked+=1
        del family
    for col,c in zip(selected,coefficients):
        for index in range(int(offsets[col]),int(offsets[col+1])):
            key,scale=unit(index);result[key]+=c*scale
    for key,c in exact_expression(n,[],[]).items():result[key]+=c
    return {k:v for k,v in result.items() if v},checked


def main():
    started=time.monotonic();data=json.loads(CRT.read_text())
    assert data['status']=='RATIONAL_PROPOSAL_PENDING_EXACT_GATE'
    expression,controls=build(data)
    print('EXACT EXPRESSION',len(expression),'CONTROLLED UNITS',controls,'SECONDS',time.monotonic()-started,flush=True)
    verifier=Verifier(budget=1000)
    out=dict(status='EXACT_GATE_STARTED',n=7,source_sha256=base.digest(CRT),engine_sha256=base.digest(ENGINE),
             family_sha256=base.digest(FAMILY),producer_sha256=base.digest(Path(__file__)),
             exact_terms=len(expression),independent_unit_controls=controls)
    try:out['status']='EXACT_TOP_IDENTITY' if verifier.check(expression) else 'RATIONAL_PROPOSAL_FAILED'
    except TimeoutError:out['status']='EXACT_GATE_BUDGET_REACHED_NO_CONCLUSION'
    out.update(symbolic_calls=verifier.calls,symbolic_seconds=time.time()-verifier.start,total_seconds=time.monotonic()-started)
    (HERE/'overnight_upper_modular_exact.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
