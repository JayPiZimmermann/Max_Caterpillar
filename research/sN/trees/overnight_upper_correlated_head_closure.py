#!/usr/bin/env python3
"""Exact entire fixed-path input space that survives the local leaf split."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
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
    start=time.monotonic();n=4;a=3;H=((0,1),(1,2),(2,3));units=set()
    for i,(u,v) in enumerate(H):
        for eps in product((1,-1),repeat=3):
            h=[0]*n;h[u]=eps[0];h[v]=-eps[0]
            E=[e if sg==1 else e[::-1] for e,sg in zip(H[:i]+H[i+1:],eps[1:])]
            units.add(old.normalize(n,h,E))
    units=sorted(units);targets=[split.target_expression(n,h,E,a) for h,E in units]
    states=split.catalog(n,H,a);keys=sorted(states);width=len(keys);rows=[];points=[];rng=random.Random(25102563)
    while len(rows)<width+len(units)+12:
        point=tuple(rng.randrange(1,15000) for _ in range(n))
        try:
            row=[family.eval_term(k,states[k][0],point) for k in keys]
            row.extend(sum(family.eval_term(k,c,point) for k,c in t.items())%family.PRIME for t in targets)
        except ZeroDivisionError:continue
        rows.append(row);points.append(point)
    source_rank=nmod_mat([r[:width] for r in rows],family.PRIME).rank()
    rr,target_rank=nmod_mat([r[width:] for r in rows],family.PRIME).rref()
    joint_rank=nmod_mat(rows,family.PRIME).rank()
    pivots=[next(j for j in range(len(units)) if rr[i,j]) for i in range(target_rank)]
    kernels=[]
    for f in sorted(set(range(len(units)))-set(pivots)):
        coefficients={f:Q(1)}
        for i,j in enumerate(pivots):
            c=old.reconstruct(int(-rr[i,f]),family.PRIME);assert c is not None
            if c:coefficients[j]=c
        expr=defaultdict(Q)
        for j,c in coefficients.items():
            for k,d in targets[j].items():expr[k]+=c*d
        assert Verifier(150).check(dict(expr))
        kernels.append([[j,str(c)] for j,c in coefficients.items()])
    safe=[j for j,(h,E) in enumerate(units) if all(a not in e for e in E)]
    safe_rank=nmod_mat([[r[width+j] for j in safe] for r in rows],family.PRIME).rank()
    safe_witnesses=[]
    for j in safe:
        h,E=units[j];sg=h[a];assert sg in (1,-1)
        newedge=(n,a) if sg==1 else (a,n)
        hnew,Enew=old.normalize(n+1,tuple(h)+(0,),E+(newedge,))
        key,c=atom_term(n+1,family.forest_atom(n+1,Enew,hnew))
        expr=defaultdict(Q,{k:-d for k,d in targets[j].items()});expr[key]+=sg*c
        assert Verifier(150).check(dict(expr))
        assert key in states
        safe_witnesses.append(dict(input_column=j,head=hnew,edges=Enew,coefficient=sg))
    assert source_rank==44 and target_rank==8 and joint_rank==48 and safe_rank==4
    assert safe_rank==source_rank+target_rank-joint_rank
    result=dict(status='EXACT_FIXED_PATH_SPLIT_CLOSURE_IS_ISOLATED_APEX_SPACE',
        source_rank=source_rank,input_span_rank=target_rank,joint_rank=joint_rank,
        isolated_apex_span_rank=safe_rank,input_units=units,input_kernels=kernels,
        safe_witnesses=safe_witnesses,points=points,prime=family.PRIME,
        source_rank_certificate_sha256=hashlib.sha256((HERE/'overnight_upper_baxter_vertex_split.json').read_bytes()).hexdigest(),
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
        scope='Among every canonical head placement and orientation on this fixed four-vertex path, exactly the isolated-apex subspace survives the specified vertex-split source span. Mixing another graph or allowing other geometric states remains open.')
    (HERE/'overnight_upper_correlated_head_closure.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'RANKS',source_rank,target_rank,joint_rank,safe_rank,'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
