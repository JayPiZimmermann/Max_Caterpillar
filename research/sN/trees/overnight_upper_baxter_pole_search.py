#!/usr/bin/env python3
"""Bounded positive search inside the fixed complete Baxter forest family.

Columns are admitted by number of new denominator poles. This is a search
order/filter, never a negative certificate for the complete family.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,random,sys,time
from flint import nmod_mat
import overnight_upper_baxter_forest_states as family
import overnight_upper_baxter_apex_geometry as geom
import overnight_upper_baxter_union as old
from overnight_upper_baxter_union_exact import expression,unit
from overnight_upper_baxter_apex_probe import atom_term

HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import Verifier

def main():
    start=time.monotonic();n=5;data=json.loads((HERE/'overnight_upper_baxter_union.json').read_text())
    graph=tuple(sorted({tuple(e) for e in data['union_graph']}|{(0,i) for i in range(1,n)}))
    target=defaultdict(Q)
    for u,c in data['target']:
        key,a=expression(n,unit(u));target[key]+=c*a
    poles={f for k in target for f,m in k[2]};catalog={}
    for basis in combinations(graph,n-2):
        if geom.components(n,basis) is None:continue
        for head in family.head_family(n,graph,basis):
            atom=family.forest_atom(n,basis,head)
            if atom is None:continue
            key,c=atom_term(n,atom);extra=sum(f not in poles for f,m in key[2])
            if extra>2:continue
            cost=(sum(abs(v) for v in head),extra,head,basis)
            if key not in catalog or cost<catalog[key][0]:catalog[key]=(cost,c,head,basis,extra)
    records=[];rng=random.Random(25102552);dest=HERE/'overnight_upper_baxter_pole_search.json'
    result=dict(status='RUNNING_BAXTER_POLE_ORDER_SEARCH',records=records,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Search filters within one unchanged complete five-state family; a negative stage is not a complete-family exclusion.')
    for allowance in (1,2):
        sources=sorted((k for k in catalog if catalog[k][-1]<=allowance),key=lambda k:catalog[k][0])
        points=[];rows=[]
        while len(rows)<len(sources)+20:
            point=tuple(rng.randrange(1,20000) for _ in range(n-1))
            try:
                row=[family.eval_term(k,catalog[k][1],point) for k in sources]
                rhs=sum(family.eval_term(k,c,point) for k,c in target.items())%family.PRIME
            except ZeroDivisionError:continue
            points.append(point);rows.append(row+[rhs])
        rr,rank=nmod_mat(rows,family.PRIME).rref()
        pivots=[next(j for j in range(len(sources)+1) if rr[i,j]) for i in range(rank)]
        gap=len(sources) in pivots
        record=dict(extra_poles_at_most=allowance,columns=len(sources),
                    ranks=[rank-int(gap),rank],status='FILTERED_MODULAR_GAP' if gap else 'FILTERED_MODULAR_INCLUSION')
        if not gap:
            proposal=[Q(0)]*len(sources)
            for i,j in enumerate(pivots):proposal[j]=old.reconstruct(int(rr[i,len(sources)]),family.PRIME)
            if all(c is not None for c in proposal):
                residual=defaultdict(Q,{k:-c for k,c in target.items()})
                for k,c in zip(sources,proposal):residual[k]+=catalog[k][1]*c
                verifier=Verifier(budget=150)
                if verifier.check(dict(residual)):
                    record.update(status='EXACT_BAXTER_APEX_FOREST_CLASS_IDENTITY',
                        selected_units=[dict(head=catalog[k][2],edges=catalog[k][3],coefficient=str(c))
                                        for k,c in zip(sources,proposal) if c],
                        principal_part_calls=verifier.calls)
                else:record['status']='RATIONAL_RECONSTRUCTION_REJECTED'
            else:record['status']='RATIONAL_RECONSTRUCTION_HEIGHT_STOP'
        records.append(record);result['seconds']=time.monotonic()-start
        dest.write_text(json.dumps(result,indent=2)+'\n')
        print('BAXTER POLE SEARCH',record['extra_poles_at_most'],record['columns'],
              record['ranks'],record['status'],'SECONDS',result['seconds'],flush=True)
        if record['status']=='EXACT_BAXTER_APEX_FOREST_CLASS_IDENTITY':break
    result['status']='COMPLETED_BOUNDED_BAXTER_POLE_ORDER_SEARCH'
    dest.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
