#!/usr/bin/env python3
"""Exact consecutive-block higher primitives with a two-page support test.

H_1 is the single gap edge. Higher targets are the genuine cocycles
R_n=sum_{i+j=n}(-1)^i H_i*H_j, with * consecutive-block concatenation.
All output rows are retained; only primitive supports have the page filter.
This is a graph-complex test, not a geometric network construction.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,time
from flint import fmpq_mat
import overnight_upper_ordered_normalized as norm

HERE=Path(__file__).parent

def clean(d):return {g:c for g,c in d.items() if c}

def crosses(e,f):
    a,b=e;c,d=f
    return a<c<b<d or c<a<d<b

def two_pages(graph):
    colors={}
    for start in range(len(graph)):
        if start in colors:continue
        colors[start]=0;stack=[start]
        while stack:
            i=stack.pop()
            for j in range(len(graph)):
                if not crosses(graph[i],graph[j]):continue
                if j in colors:
                    if colors[j]==colors[i]:return False
                else:colors[j]=1-colors[i];stack.append(j)
    return True

def delta(q,chain):
    out=defaultdict(Q)
    for g,c in chain.items():
        for f,v in norm.differential(q,g).items():out[f]+=c*v
    return clean(out)

def multiply(left,right,left_q):
    out=defaultdict(Q)
    for a,c in left.items():
        for b,d in right.items():
            out[a+tuple((u+left_q,v+left_q) for u,v in b)]+=c*d
    return clean(out)

def serialize(chain):return [[g,str(c)] for g,c in chain.items() if c]

def solve(k,target):
    source=[g for g in norm.basis(k+1,k) if two_pages(g)]
    destination=norm.basis(k+2,k)
    columns=[norm.differential(k+1,g) for g in source]
    # Convert through strings because python-flint does not accept Fraction.
    rows=[[column.get(g,0) for column in columns]+[str(target.get(g,0))] for g in destination]
    rr,rank=fmpq_mat(rows).rref()
    pivots=[next(j for j in range(len(source)+1) if rr[i,j]) for i in range(rank)]
    gap=len(source) in pivots
    record=dict(k=k,source_q=k+1,source_columns=len(source),
                all_source_columns=len(norm.basis(k+1,k)),target_rows=len(destination),
                target_terms=len(target),ranks=[rank-int(gap),rank],target=serialize(target))
    if gap:return None,record
    coeff=[Q(0)]*len(source)
    for i,p in enumerate(pivots):coeff[p]=Q(str(rr[i,len(source)]))
    primitive={g:c for g,c in zip(source,coeff) if c}
    assert delta(k+1,primitive)==target
    assert all(two_pages(g) for g in primitive)
    record.update(primitive_terms=len(primitive),primitive=serialize(primitive),
                  status='EXACT_TWO_PAGE_HIGHER_PRIMITIVE')
    return primitive,record

def main():
    start=time.monotonic();H={1:{((0,1),):Q(1)}};records=[]
    receipt=dict(status='RUNNING_TWO_PAGE_HIGHER_PRIMITIVE_TEST',records=records,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Tests one explicitly chosen sequence of higher primitives; even a positive sequence through k5 does not prove uniform two-page closure or a geometric realization.')
    dest=HERE/'overnight_upper_ordered_ainfty_pages.json'
    for k in range(2,6):
        target=defaultdict(Q)
        for i in range(1,k):
            for g,c in multiply(H[i],H[k-i],i+1).items():target[g]+=(-1)**i*c
        target=clean(target)
        assert not delta(k+2,target),'Stasheff cocycle identity'
        primitive,record=solve(k,target)
        records.append(record);receipt['seconds']=time.monotonic()-start
        dest.write_text(json.dumps(receipt,indent=2)+'\n')
        print('TWO-PAGE HIGHER PRIMITIVE',k,record['ranks'],record.get('primitive_terms'),
              'SECONDS',receipt['seconds'],flush=True)
        if primitive is None:
            record['status']='EXACT_TWO_PAGE_HIGHER_PRIMITIVE_FAILURE';break
        H[k]=primitive
    receipt['status']='COMPLETED_TWO_PAGE_HIGHER_PRIMITIVE_TEST'
    receipt['seconds']=time.monotonic()-start
    dest.write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
