#!/usr/bin/env python3
"""Max-substitute the complete two-edge orientation-difference cycle.

Unlike an individual atom, all four terms cancel both the constant and
linear outer tails. Test the same unchanged vertex-split tree sources.
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
    start=time.monotonic();n=4;head=(-1,1,0,0);edges=((1,2),(2,3));tree=((1,0),)+edges
    records=[];rng=random.Random(25102561)
    for a in (1,2,3):
        target=defaultdict(Q)
        for signs in product((1,-1),repeat=2):
            oriented=[(u,v) if sign==1 else (v,u) for (u,v),sign in zip(edges,signs)]
            for key,c in split.target_expression(n,head,oriented,a).items():target[key]+=signs[0]*signs[1]*c
        states=split.catalog(n,tree,a);keys=sorted(states);rows=[];points=[]
        while len(rows)<len(keys)+12:
            point=tuple(rng.randrange(1,15000) for _ in range(n))
            try:
                row=[family.eval_term(k,states[k][0],point) for k in keys]
                rhs=sum(family.eval_term(k,c,point) for k,c in target.items())%family.PRIME
            except ZeroDivisionError:continue
            rows.append(row+[rhs]);points.append(point)
        rr,rank=nmod_mat(rows,family.PRIME).rref()
        pivots=[next(j for j in range(len(keys)+1) if rr[i,j]) for i in range(rank)]
        gap=len(keys) in pivots
        record=dict(split_label=a,columns=len(keys),ranks=[rank-int(gap),rank],points=points,
            status='MODULAR_CORRELATED_SPLIT_GAP' if gap else 'MODULAR_CORRELATED_SPLIT_INCLUSION')
        if not gap:
            cs={}
            for i,j in enumerate(pivots):
                c=old.reconstruct(int(rr[i,len(keys)]),family.PRIME);assert c is not None
                if c:cs[j]=c
            residual=defaultdict(Q,{k:-c for k,c in target.items()})
            for j,c in cs.items():residual[keys[j]]+=c*states[keys[j]][0]
            V=Verifier(150);assert V.check(dict(residual))
            record.update(status='EXACT_CORRELATED_VERTEX_SPLIT_IDENTITY',calls=V.calls,
                selected=[dict(head=states[keys[j]][1],edges=states[keys[j]][2],coefficient=str(c)) for j,c in cs.items()])
        else:
            # The frozen individual-atom receipt proves the complete source
            # rank bound globally; the same source catalogue is used here.
            prior=json.loads((HERE/'overnight_upper_baxter_vertex_split.json').read_text())
            r=next(r for r in prior['records'] if r['split_label']==a)
            assert r['sources']==[dict(head=list(states[k][1]),edges=[list(e) for e in states[k][2]]) for k in keys]
            assert r['ranks'][0]==rank-1
            record.update(status='EXACT_CORRELATED_VERTEX_SPLIT_OBSTRUCTION',
                source_rank_certificate='overnight_upper_baxter_vertex_split.json',
                source_rank_sha256=hashlib.sha256((HERE/'overnight_upper_baxter_vertex_split.json').read_bytes()).hexdigest())
        records.append(record)
        result=dict(status='BOUNDED_CORRELATED_VERTEX_SPLIT_GATE',head=head,edges=edges,records=records,
            prime=family.PRIME,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            seconds=time.monotonic()-start,
            scope='Complete two-edge orientation-difference cycle, with exact zero outer tails, versus the frozen vertex-split tree catalogue. No uniform recurrence claim.')
        (HERE/'overnight_upper_correlated_split.json').write_text(json.dumps(result,indent=2)+'\n')
        print('CORRELATED SPLIT',a,record['ranks'],record['status'],'TERMS',len(record.get('selected',[])),
              'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
