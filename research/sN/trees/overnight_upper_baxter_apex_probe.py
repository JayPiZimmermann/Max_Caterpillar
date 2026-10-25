#!/usr/bin/env python3
"""Actual Baxter class in full-rank apex-star/union zonotope units."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json,random,sys,time
from flint import nmod_mat
import overnight_upper_baxter_apex_geometry as geom
import overnight_upper_baxter_union as old
from overnight_upper_baxter_union_exact import expression,unit

HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import term,Verifier
PRIME=1000003

def atom_term(n,atom):
    coefficient,num,den=atom
    numerator=tuple(num[i]-num[0] for i in range(1,n))+(0,)
    denominator=[(tuple(f[i]-f[0] for i in range(1,n))+(0,),1) for f in den]
    return term(coefficient,numerator,n-4,denominator)

def evaluate(n,atom,point):
    c,num,den=atom;p=PRIME
    denominator=1
    for f in den:
        v=sum(a*b for a,b in zip(f,point))%p
        if not v:raise ZeroDivisionError
        denominator=denominator*v%p
    numerator=sum(a*b for a,b in zip(num,point))%p
    return c*pow(numerator,n-4,p)*pow(denominator,-1,p)%p

def main():
    start=time.monotonic();n=5
    oldpath=HERE/'overnight_upper_baxter_union.json';data=json.loads(oldpath.read_text())
    control=json.loads((HERE/'overnight_upper_baxter_apex_controls.json').read_text())
    assert control['status']=='DIRECT_VERTEX_FACET_GRAPHIC_TILING_CONTROLS_PASSED'
    assert control['evaluator_sha256']==hashlib.sha256((HERE/'overnight_upper_baxter_apex_geometry.py').read_bytes()).hexdigest()
    graph=tuple(sorted({tuple(e) for e in data['union_graph']}|{(0,i) for i in range(1,n)}))
    heads=set()
    for root in range(1,n):
        for bits in product((0,1),repeat=len(graph)):
            h=[-1]+[0]*(n-1);h[root]=1
            for b,(i,j) in zip(bits,graph):
                if b:h[i]-=1;h[j]+=1
            heads.add(tuple(h))
    atom_inventory=[];lookup={};columns=[];kept=[]
    for head in sorted(heads):
        atoms=geom.atoms(n,graph,head)
        if not atoms:continue
        indices=[]
        for atom in atoms:
            if atom not in lookup:lookup[atom]=len(atom_inventory);atom_inventory.append(atom)
            indices.append(lookup[atom])
        kept.append(head);columns.append(indices)
    target_forms=[(old.factors(n,unit(u)),c) for u,c in data['target']]
    points=[];rows=[];rng=random.Random(25102550)
    while len(rows)<len(columns)+20:
        rest=[rng.randrange(1,30000) for _ in range(n-1)];point=(-sum(rest),*rest)
        try:
            values=[evaluate(n,a,point) for a in atom_inventory]
            row=[sum(values[i] for i in col)%PRIME for col in columns]
            target=sum(c*old.value(n,f,point,PRIME) for f,c in target_forms)%PRIME
        except ZeroDivisionError:continue
        points.append(point);rows.append(row+[target])
    rr,rank=nmod_mat(rows,PRIME).rref()
    pivots=[next(j for j in range(len(columns)+1) if rr[i,j]) for i in range(rank)]
    gap=len(columns) in pivots
    result=dict(status='MODULAR_BAXTER_APEX_STAR_GAP' if gap else 'MODULAR_BAXTER_APEX_STAR_INCLUSION',
        n=n,class_words=data['class_words'],graph=graph,all_normalized_heads=len(heads),
        nonshallow_heads=kept,source_columns=len(columns),forest_atoms=len(atom_inventory),
        ranks=[rank-int(gap),rank],prime=PRIME,points=points,
        source_certificate_sha256=hashlib.sha256(oldpath.read_bytes()).hexdigest(),
        evaluator_sha256=control['evaluator_sha256'],
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Full zonotope units with canonical root/apex heads and all inner orientations. A gap does not exclude all graph face states or arbitrary heads. A positive top identity still requires a uniform recurrence and lower-dimensional corrections.')
    if not gap:
        proposal=[Q(0)]*len(columns)
        for i,j in enumerate(pivots):proposal[j]=old.reconstruct(int(rr[i,len(columns)]),PRIME)
        if all(c is not None for c in proposal):
            residual=defaultdict(Q)
            for col,c in zip(columns,proposal):
                if c:
                    for i in col:
                        key,a=atom_term(n,atom_inventory[i]);residual[key]+=c*a
            for u,c in data['target']:
                key,a=expression(n,unit(u));residual[key]-=c*a
            verifier=Verifier(budget=150)
            if verifier.check(dict(residual)):
                result.update(status='EXACT_BAXTER_APEX_STAR_CLASS_IDENTITY',
                              coefficients=[[i,str(c)] for i,c in enumerate(proposal) if c],
                              selected_heads=[[kept[i],str(c)] for i,c in enumerate(proposal) if c],
                              principal_part_calls=verifier.calls)
            else:result['status']='BAXTER_APEX_STAR_RECONSTRUCTION_FAILED'
        else:result['status']='BAXTER_APEX_STAR_RECONSTRUCTION_HEIGHT_STOP'
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_baxter_apex_probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'FULL',len(heads),'NONSHALLOW',len(columns),'ATOMS',len(atom_inventory),
          'RANKS',result['ranks'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
