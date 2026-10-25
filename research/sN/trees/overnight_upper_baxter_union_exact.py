#!/usr/bin/env python3
"""Exact kernel gate for the smallest Baxter/union-zonotope bridge test."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,sys,time
from flint import nmod_mat
import overnight_upper_baxter_union as probe

HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import term,Verifier

def unit(data):
    return tuple(data[0]),tuple(map(tuple,data[1]))

def expression(n,u):
    forms=probe.factors(n,u)
    denominator=[(tuple(f[i]-f[0] for i in range(1,n))+(0,),1) for f in forms]
    key,c=term(Q(1),(1,)*(n-1)+(0,),n-4,denominator)
    return key,c

def main():
    start=time.monotonic();path=HERE/'overnight_upper_baxter_union.json'
    data=json.loads(path.read_text());n=data['labels'];p=data['prime']
    sources=list(map(unit,data['sources']))
    forms=[probe.factors(n,u) for u in sources]
    target=[(probe.factors(n,unit(u)),c) for u,c in data['target']]
    rows=[]
    for point in data['points']:
        row=[probe.value(n,f,point,p) for f in forms]
        rhs=sum(c*probe.value(n,f,point,p) for f,c in target)%p
        rows.append(row+[rhs])
    rr,rank=nmod_mat(rows,p).rref()
    pivots=[next(j for j in range(len(sources)+1) if rr[i,j]) for i in range(rank)]
    assert pivots[-1]==len(sources)
    ordinary_pivots=pivots[:-1]
    free=sorted(set(range(len(sources)))-set(ordinary_pivots))
    expressions=[expression(n,u) for u in sources]
    kernels=[];calls=0
    for free_index in free:
        coefficients={free_index:Q(1)}
        for i,pivot in enumerate(ordinary_pivots):
            value=probe.reconstruct(int(-rr[i,free_index]),p)
            assert value is not None,'rational reconstruction is only a proposal'
            if value:coefficients[pivot]=value
        expr={}
        for j,value in coefficients.items():
            key,c=expressions[j];expr[key]=expr.get(key,Q(0))+value*c
        verifier=Verifier(budget=max(1,150-(time.monotonic()-start)))
        assert verifier.check(expr),('exact rational identity',free_index)
        calls+=verifier.calls
        kernels.append(dict(free_column=free_index,coefficients=[[j,str(c)] for j,c in sorted(coefficients.items())]))
        print('EXACT BAXTER KERNEL',len(kernels),'OF',len(free),'TERMS',len(coefficients),
              'SECONDS',time.monotonic()-start,flush=True)
    assert len(kernels)==len(sources)-data['ranks'][0]
    result=dict(status='EXACT_SMALLEST_BAXTER_CANONICAL_CYCLE_BRIDGE_OBSTRUCTION',
                ranks=data['ranks'],columns=len(sources),independent_exact_kernels=kernels,
                principal_part_calls=calls,seconds=time.monotonic()-start,
                source_certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Rejects this one proposed Baxter-class image in the canonical union-cycle/five-state span. General noncanonical heads, weights, and a different geometric bridge remain open.')
    (HERE/'overnight_upper_baxter_union_exact.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
