#!/usr/bin/env python3
"""Cheapest completion of the failed leaf max-substitution rule.

Allow all three spanning trees of the triangle on the old leaf, new leaf,
and its old neighbour, with every canonical head placement/orientation.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib,json,random,time
from flint import nmod_mat
import overnight_upper_baxter_vertex_split as split
import overnight_upper_baxter_forest_states as family
import overnight_upper_baxter_union as old
from overnight_upper_baxter_apex_probe import atom_term
from rational_identity import Verifier
HERE=Path(__file__).parent

def main():
    start=time.monotonic();states={};n=5
    for localtree in combinations(((2,3),(2,4),(3,4)),2):
        tree=((0,1),(1,2))+localtree
        for i,(u,v) in enumerate(tree):
            free=tree[:i]+tree[i+1:]
            for signs in product((1,-1),repeat=4):
                head=[0]*n;head[u]=signs[0];head[v]=-signs[0]
                edges=[(s,t) if eps==1 else (t,s) for (s,t),eps in zip(free,signs[1:])]
                h,E=old.normalize(n,head,edges);atom=family.forest_atom(n,E,h)
                key,c=atom_term(n,atom);states.setdefault(key,(c,h,E))
    keys=sorted(states);target=split.target_expression(4,(-1,1,0,0),((1,2),(2,3)),3)
    rng=random.Random(25102558);points=[];rows=[]
    while len(rows)<len(keys)+16:
        point=tuple(rng.randrange(1,12000) for _ in range(4))
        try:
            row=[family.eval_term(k,states[k][0],point) for k in keys]
            rhs=sum(family.eval_term(k,c,point) for k,c in target.items())%family.PRIME
        except ZeroDivisionError:continue
        points.append(point);rows.append(row+[rhs])
    rr,rank=nmod_mat(rows,family.PRIME).rref()
    pivots=[next(j for j in range(len(keys)+1) if rr[i,j]) for i in range(rank)]
    gap=len(keys) in pivots
    result=dict(status='MODULAR_TRIANGLE_COMPLETION_GAP' if gap else 'MODULAR_TRIANGLE_COMPLETION_INCLUSION',
        columns=len(keys),ranks=[rank-int(gap),rank],points=points,prime=family.PRIME,
        sources=[dict(head=states[k][1],edges=states[k][2]) for k in keys])
    if gap:
        kernels=[]
        for f in sorted(set(range(len(keys)))-set(pivots)):
            cs={f:Q(1)}
            for i,j in enumerate(pivots[:-1]):
                c=old.reconstruct(int(-rr[i,f]),family.PRIME);assert c is not None
                if c:cs[j]=c
            residual=defaultdict(Q)
            for j,c in cs.items():residual[keys[j]]+=c*states[keys[j]][0]
            assert Verifier(150).check(dict(residual))
            kernels.append([[j,str(c)] for j,c in cs.items()])
        result.update(status='EXACT_TRIANGLE_COMPLETION_OBSTRUCTION',kernels=kernels)
    else:
        cs={}
        for i,j in enumerate(pivots):
            c=old.reconstruct(int(rr[i,len(keys)]),family.PRIME);assert c is not None
            if c:cs[j]=c
        residual=defaultdict(Q,{k:-c for k,c in target.items()})
        for j,c in cs.items():residual[keys[j]]+=c*states[keys[j]][0]
        assert Verifier(150).check(dict(residual))
        result.update(status='EXACT_TRIANGLE_COMPLETION_IDENTITY',
            selected=[dict(head=states[keys[j]][1],edges=states[keys[j]][2],coefficient=str(c)) for j,c in cs.items()])
    result.update(seconds=time.monotonic()-start,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Exact smallest necessary gate for canonical head placements on local triangle spanning trees. Broader cyclic formal states and noncanonical heads remain outside this test.')
    (HERE/'overnight_upper_baxter_vertex_completion.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'RANKS',result['ranks'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
