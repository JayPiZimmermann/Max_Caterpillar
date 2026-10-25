#!/usr/bin/env python3
"""Search the complete five-state forest normal form of a Baxter apex graph.

The target-pole filter is only a positive-search heuristic. A gap does not
exclude the complete family. Any found identity is gated symbolically.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,math,random,sys,time
from flint import nmod_mat
import overnight_upper_baxter_apex_geometry as geom
import overnight_upper_baxter_union as old
from overnight_upper_baxter_union_exact import expression,unit
from overnight_upper_baxter_apex_probe import atom_term
HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import Verifier
PRIME=1000003

def head_family(n,graph,basis):
    heads={tuple(int(i==r)-int(i==0) for i in range(n)) for r in range(1,n)}
    for edge in graph:
        vector=geom.diff(n,*edge)
        choices=(-1,0) if edge in basis else (-1,0,1)
        heads={tuple(a+t*b for a,b in zip(h,vector)) for h in heads for t in choices}
    return heads

def forest_atom(n,basis,head):
    comps=geom.components(n,basis);assert comps is not None and len(comps)==2
    S=comps[0];height=sum(head[i] for i in S)
    if not height:return None
    if height>0:S=comps[1];height=-height
    mask=sum(1<<i for i in S);c=-height;forms=[]
    for away,epsilon in geom.cuts(n,basis,mask):
        H=sum(head[i] for i in away)
        for t in (H,H+epsilon):
            forms.append(tuple(c*int(i in away)+t*int(i in S) for i in range(n)))
    return (c**(n-1),tuple(-int(i in S) for i in range(n)),tuple(forms))

def eval_term(key,coefficient,point):
    num,power,den=key;p=PRIME
    dot=lambda f:sum(a*b for a,b in zip(f[:-1],point))+f[-1]
    denominator=1
    for f,m in den:
        v=dot(f)%p
        if not v:raise ZeroDivisionError
        denominator=denominator*pow(v,m,p)%p
    c=coefficient.numerator*pow(coefficient.denominator,-1,p)%p
    return c*pow(dot(num)%p,power,p)*pow(denominator,-1,p)%p

def main():
    start=time.monotonic();n=5
    data=json.loads((HERE/'overnight_upper_baxter_union.json').read_text())
    graph=tuple(sorted({tuple(e) for e in data['union_graph']}|{(0,i) for i in range(1,n)}))
    target=defaultdict(Q)
    for u,c in data['target']:
        key,a=expression(n,unit(u));target[key]+=c*a
    poles={f for key in target for f,m in key[2]}
    sources={};forest_count=raw_heads=nonzero_heads=compatible=0
    for basis in combinations(graph,n-2):
        if geom.components(n,basis) is None:continue
        forest_count+=1
        heads=head_family(n,graph,basis);raw_heads+=len(heads)
        for head in heads:
            atom=forest_atom(n,basis,head)
            if atom is None:continue
            nonzero_heads+=1
            key,c=atom_term(n,atom)
            if not all(f in poles for f,m in key[2]):continue
            compatible+=1
            if key not in sources:sources[key]=(c,head,basis)
    source=list(sources);values=[sources[k][0] for k in source]
    print('FOREST INVENTORY',forest_count,raw_heads,nonzero_heads,compatible,len(source),
          'SECONDS',time.monotonic()-start,flush=True)
    rng=random.Random(25102551);points=[];rows=[]
    while len(rows)<len(source)+16:
        point=tuple(rng.randrange(1,20000) for _ in range(n-1))
        try:
            row=[eval_term(k,c,point) for k,c in zip(source,values)]
            rhs=sum(eval_term(k,c,point) for k,c in target.items())%PRIME
        except ZeroDivisionError:continue
        rows.append(row+[rhs]);points.append(point)
    rr,rank=nmod_mat(rows,PRIME).rref()
    pivots=[next(j for j in range(len(source)+1) if rr[i,j]) for i in range(rank)]
    gap=len(source) in pivots
    result=dict(status='DIAGNOSTIC_TARGET_POLE_FOREST_GAP' if gap else 'MODULAR_TARGET_POLE_FOREST_INCLUSION',
        n=n,graph=graph,forests=forest_count,normalized_head_descriptions=raw_heads,
        nonzero_descriptions=nonzero_heads,target_pole_compatible_descriptions=compatible,
        source_columns=len(source),target_poles=len(poles),ranks=[rank-int(gap),rank],
        points=points,prime=PRIME,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='All five-state normalized forest heads are enumerated, but only columns without new poles are tested. Negative result is a filtered diagnostic. A positive identity is checked exactly.')
    if not gap:
        proposal=[Q(0)]*len(source)
        for i,j in enumerate(pivots):proposal[j]=old.reconstruct(int(rr[i,len(source)]),PRIME)
        if all(c is not None for c in proposal):
            residual=defaultdict(Q,{k:-c for k,c in target.items()})
            for k,a,c in zip(source,values,proposal):residual[k]+=a*c
            verifier=Verifier(budget=150)
            if verifier.check(dict(residual)):
                result.update(status='EXACT_BAXTER_APEX_FOREST_CLASS_IDENTITY',
                    selected_units=[dict(head=sources[k][1],edges=sources[k][2],coefficient=str(c))
                                    for k,c in zip(source,proposal) if c],
                    principal_part_calls=verifier.calls)
            else:result['status']='FOREST_RECONSTRUCTION_REJECTED'
        else:result['status']='FOREST_RECONSTRUCTION_HEIGHT_STOP'
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_baxter_forest_states.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'RANKS',result['ranks'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
