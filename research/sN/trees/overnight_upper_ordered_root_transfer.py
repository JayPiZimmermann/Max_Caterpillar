#!/usr/bin/env python3
"""Exact geometric cube controls for the one-root-transfer homotopy."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import hashlib,json,time
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_single_facet as single
import overnight_upper_product_family as base

HERE=Path(__file__).parent

def add(*weighted):
    out=defaultdict(int)
    for scale,chain in weighted:
        for term,c in chain.items():out[term]+=scale*c
    return coherent.clean(out)

def z(n,i,j):
    assert i>j>0
    abstract={((0,)*(n-1),((1,i,j),)):1}
    return contraction.from_abstract(contraction.expand_basis(abstract,n,False),n)

def edge(n,i,j):
    item=base.normalize_cube((0,)*n,[base.diff(n,i,j)],1)
    return {item[0]:item[1]}

def product(chains,n):
    out={((0,)*n,()):1}
    for c in chains:out=coherent.multiply(out,c)
    return out

def local(n,i,j):
    I,J=i+1,j+1
    actual=single.coface(z(n,i,j),n,0)
    constant=add((1,z(n+1,I,J)),(-1,z(n+1,I,1)),(1,z(n+1,J,1)))
    primitive=coherent.multiply(edge(n+1,1,J),add((-1,z(n+1,I,1)),(1,z(n+1,J,1))))
    assert coherent.boundary(primitive)==add((1,actual),(-1,constant))
    return actual,constant,primitive

def main():
    start=time.monotonic();records=[]
    n=5;pairs=[(j,i) for i,j in combinations(range(1,n),2)]
    checks=0
    for k in (1,2,3,4):
        descriptors=list(combinations(pairs,k))
        if k==4:descriptors=descriptors[:3]
        maximum=0
        for descriptor in descriptors:
            factors=[local(n,i,j) for i,j in descriptor]
            primitive={}
            for t,(_,_,p) in enumerate(factors):
                term=product([f[0] for f in factors[:t]]+[p]+[f[1] for f in factors[t+1:]],n+1)
                primitive=add((1,primitive),((-1)**t,term))
            actual=single.coface(product([z(n,i,j) for i,j in descriptor],n),n,0)
            constant=product([f[1] for f in factors],n+1)
            assert coherent.boundary(primitive)==add((1,actual),(-1,constant))
            assert len(primitive)<=9**k-3**k
            maximum=max(maximum,len(primitive));checks+=1
        records.append(dict(k=k,products_checked=len(descriptors),complete=k<=3,
                            max_actual_primitive_cubes=maximum,theoretical_bound=9**k-3**k))
        print('ROOT TRANSFER',records[-1],'SECONDS',time.monotonic()-start,flush=True)
    result=dict(status='EXACT_ORIGINAL_CUBE_ROOT_TRANSFER_HOMOTOPY_CONTROLS',
                records=records,checks=checks,seconds=time.monotonic()-start,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Uniform local and product homotopy; the displayed exponential bound applies to one full closed-wedge transfer. No uniform bound on the number of correction wedges over all arities is asserted.')
    (HERE/'overnight_upper_ordered_root_transfer.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
