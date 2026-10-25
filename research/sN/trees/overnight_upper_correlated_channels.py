#!/usr/bin/env python3
"""Find every tail-cancelling orientation channel closed by the leaf split.

The four old orientations and unchanged local source catalogue are fixed.
No new head, graph or numerical alphabet is introduced.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json,random,time
from flint import nmod_mat
import overnight_upper_baxter_vertex_split as split
import overnight_upper_baxter_forest_states as family
import overnight_upper_baxter_union as old
from rational_identity import Verifier
HERE=Path(__file__).parent

def main():
    start=time.monotonic();n=4;head=(-1,1,0,0);edges=((1,2),(2,3));a=3
    signs=list(product((1,-1),repeat=2));targets=[]
    for eps in signs:
        E=[(u,v) if e==1 else (v,u) for (u,v),e in zip(edges,eps)]
        targets.append(split.target_expression(n,head,E,a))
    states=split.catalog(n,((1,0),)+edges,a);keys=sorted(states);width=len(keys)
    rng=random.Random(25102562);rows=[];points=[]
    while len(rows)<width+20:
        point=tuple(rng.randrange(1,15000) for _ in range(n))
        try:
            row=[family.eval_term(k,states[k][0],point) for k in keys]
            row.extend(sum(family.eval_term(k,c,point) for k,c in t.items())%family.PRIME for t in targets)
        except ZeroDivisionError:continue
        rows.append(row);points.append(point)
    ordinary=nmod_mat([r[:width] for r in rows],family.PRIME).rank()
    target_rank=nmod_mat(rows,family.PRIME).rank()
    rows.append([0]*width+[1]*4) # sum c_i=0, hence both substituted tails shallow
    rr,rank=nmod_mat(rows,family.PRIME).rref()
    pivots=[next(j for j in range(width+4) if rr[i,j]) for i in range(rank)]
    free=[j for j in range(width,width+4) if j not in pivots];relations=[]
    for f in free:
        coefficients={f:Q(1)}
        for i,j in enumerate(pivots):
            c=old.reconstruct(int(-rr[i,f]),family.PRIME);assert c is not None
            if c:coefficients[j]=c
        residual=defaultdict(Q);tail=[Q(0)]*4
        for j,c in coefficients.items():
            if j<width:
                residual[keys[j]]+=c*states[keys[j]][0]
            else:
                tail[j-width]=c
                for k,d in targets[j-width].items():residual[k]+=c*d
        assert sum(tail)==0
        V=Verifier(150);assert V.check(dict(residual))
        relations.append(dict(target_orientation_coefficients=list(map(str,tail)),
            source_terms=[dict(head=states[keys[j]][1],edges=states[keys[j]][2],coefficient=str(-c))
                          for j,c in coefficients.items() if j<width],calls=V.calls))
    result=dict(status='EXACT_CLOSED_CORRELATED_ORIENTATION_CHANNELS',old_head=head,old_edges=edges,
        orientations=signs,split_label=a,source_columns=width,source_rank=ordinary,
        source_plus_targets_rank=target_rank,with_tail_constraint_rank=rank,
        closed_tail_cancelling_channel_dimension=len(free),relations=relations,points=points,prime=family.PRIME,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
        scope='Exact identities for the recovered channels and a modular upper bound on their complete dimension, using the independently proved source rank. No uniform grafting or whole-function closure is inferred.')
    (HERE/'overnight_upper_correlated_channels.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'RANKS',ordinary,target_rank,rank,'CHANNELS',len(free),
          'COEFFICIENTS',[r['target_orientation_coefficients'] for r in relations],
          'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
