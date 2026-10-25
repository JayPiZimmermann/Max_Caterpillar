#!/usr/bin/env python3
"""Actual single-coface recurrence with complete prior homology-gauge freedom.

Tests whether its next closed correction can have at most two factors
depending on root0, using Z=Z(labels excluding0) + span Gamma(0,1,j).
This deliberately permits every nonroot triangle; no interval restriction.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib,json,math,time
from flint import fmpq_mat
import overnight_upper_ordered_augmentation as aug
import overnight_upper_ordered_coherent as coh
import overnight_upper_ordered_contraction as con
import overnight_upper_ordered_single_facet as single
import overnight_upper_ordered_root_transfer as transfer
import overnight_upper_triangle_attachments as attachment

HERE=Path(__file__).parent

def add(*weighted):
    out=defaultdict(Q)
    for scale,chain in weighted:
        for key,c in chain.items():out[key]+=scale*c
    return coh.clean(out)

def lift(n,wedge_chain):
    out={}
    for wedge,c in wedge_chain.items():
        abstract={((0,)*(n-1),tuple((1,i,j) for i,j in wedge)):1}
        chain=con.from_abstract(con.expand_basis(abstract,n,False),n)
        out=add((1,out),(c,chain))
    return out

def A(chain,n):
    scale=math.lcm(*(Q(c).denominator for c in chain.values()))
    integral={key:int(scale*c) for key,c in chain.items()}
    result,_=con.contract(single.coface(integral,n,0),n+1)
    return {key:Q(c,scale) for key,c in result.items()}

def pF(chain):
    out=defaultdict(Q)
    for (h,edges),c in chain.items():
        wedge=tuple((e.index(1)+1,e.index(-1)+1) for e in edges)
        sign=(-1)**sum(wedge[i]>wedge[j] for i,j in combinations(range(len(wedge)),2))
        out[tuple(sorted(wedge))]+=sign*c
    return coh.clean(out)

def solve(n,targets):
    k=n-2;source=list(combinations(aug.cycle_basis(n),k))
    destination=list(combinations(aug.cycle_basis(n+1),k))
    columns=[aug.delta_wedge(n,w) for w in source]
    rr,rank=fmpq_mat([[c.get(w,0) for c in columns]+[str(t.get(w,0)) for t in targets] for w in destination]).rref()
    pivots=[next(j for j in range(len(source)+len(targets)) if rr[i,j]) for i in range(rank)]
    assert all(p<len(source) for p in pivots)
    solutions=[{source[p]:Q(str(rr[i,len(source)+t])) for i,p in enumerate(pivots)
                if rr[i,len(source)+t]} for t in range(len(targets))]
    kernels=[]
    for free in sorted(set(range(len(source)))-set(pivots)):
        v={source[free]:Q(1)}
        for i,p in enumerate(pivots):
            if rr[i,free]:v[source[p]]=-Q(str(rr[i,free]))
        kernels.append(v)
    return solutions,kernels,dict(labels=n,columns=len(source),rank=rank,kernel_dimension=len(kernels))

def expand_factors(factors):
    out=defaultdict(int)
    for choices in product(*(tuple(f.items()) for f in factors)):
        wedge=[g for g,c in choices]
        if len(set(wedge))<len(wedge):continue
        coefficient=math.prod(c for g,c in choices)
        coefficient*=(-1)**sum(wedge[i]>wedge[j] for i,j in combinations(range(len(wedge)),2))
        out[tuple(sorted(wedge))]+=coefficient
    return coh.clean(out)

def bounded_basis(n,b):
    dependent=[{(i,1):1} for i in range(2,n)]
    free=[{(i,j):1,(i,1):-1,(j,1):1} for i in range(2,n) for j in range(2,i)]
    result=[]
    for count in range(b+1):
        for left in combinations(dependent,count):
            for right in combinations(free,n-2-count):
                result.append(expand_factors(left+right))
    return result

def d_wedges(n,chain):
    out=defaultdict(Q)
    for w,c in chain.items():
        for v,b in aug.delta_wedge(n,w).items():out[v]+=c*b
    return coh.clean(out)

def serialize(chain):return [[g,str(c)] for g,c in chain.items()]

def main():
    start=time.monotonic()
    X3=coh.multiply(transfer.edge(4,1,0),attachment.raw_chain(4,(((1,2,3),1,1),)))
    (c3,),K3,r3=solve(4,[pF(X3)]);assert not K3
    X4=A(add((1,X3),(-1,lift(4,c3))),4)
    (c4,),K4,r4=solve(5,[pF(X4)]);assert len(K4)==1
    X5=A(add((1,X4),(-1,lift(5,c4))),5)
    X5var=A(add((-1,lift(5,K4[0]))),5)
    target=pF(X5);variation=pF(X5var)
    columns=bounded_basis(6,2)
    images=[d_wedges(6,c) for c in columns]
    rows=list(combinations(aug.cycle_basis(7),4))
    rr,rank=fmpq_mat([[str(c.get(w,0)) for c in images]+[str(-variation.get(w,0)),str(target.get(w,0))] for w in rows]).rref()
    variables=len(columns)+1
    pivots=[next(j for j in range(variables+1) if rr[i,j]) for i in range(rank)]
    gap=variables in pivots
    result=dict(status='EXACT_ACTUAL_ROOT_INCIDENCE_TWO_FAILURE' if gap else 'EXACT_ACTUAL_ROOT_INCIDENCE_TWO_SUCCESS',
        earlier_full_coverage=[r3,r4],prior_gauge_dimension=1,bounded_columns=len(columns),
        root_dependent_factors_at_most=2,all_target_rows=len(rows),ranks=[rank-int(gap),rank],
        target=serialize(target),gauge_variation=serialize(variation),
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Complete earlier homology gauges for the fixed H and canonical closed lift. The bounded-root family permits arbitrary nonroot triangles. This does not cover other contractions or closed representatives outside ker H.')
    if gap:
        dualrows=[[str(c.get(w,0)) for w in rows]+[0] for c in images]
        dualrows += [[str(variation.get(w,0)) for w in rows]+[0]]
        dualrows += [[str(target.get(w,0)) for w in rows]+[1]]
        dr,drank=fmpq_mat(dualrows).rref();dual=[Q(0)]*len(rows)
        for i in range(drank):
            p=next(j for j in range(len(rows)+1) if dr[i,j]);assert p<len(rows)
            dual[p]=Q(str(dr[i,len(rows)]))
        pairing=lambda c:sum(v*c.get(w,0) for w,v in zip(rows,dual))
        assert all(pairing(c)==0 for c in images)
        assert pairing(variation)==0 and pairing(target)==1
        result['separator']=[[w,str(v)] for w,v in zip(rows,dual) if v]
    else:
        values=[Q(0)]*variables
        for i,p in enumerate(pivots):values[p]=Q(str(rr[i,variables]))
        c5=add(*((c,v) for c,v in zip(values,columns)))
        assert d_wedges(6,c5)==add((1,target),(values[-1],variation))
        result.update(prior_gauge=str(values[-1]),bounded_coefficients=list(map(str,values[:-1])),
                      correction=serialize(c5))
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_root_incidence.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'RANKS',result['ranks'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
