#!/usr/bin/env python3
"""Necessary exact gate for a local max-coordinate vertex-split rule."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json,random,sys,time
from flint import nmod_mat
import overnight_upper_baxter_forest_states as family
import overnight_upper_baxter_union as old
from overnight_upper_baxter_apex_probe import atom_term
HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import term,Verifier

def target_expression(n,head,edges,a):
    h,E=old.normalize(n,head,edges);atom=family.forest_atom(n,E,h);assert atom
    c,num,den=atom
    def lift(f):return tuple(f)+(f[a],)
    def affine(f):return tuple(f[i]-f[0] for i in range(1,n+1))+(0,)
    result=defaultdict(Q)
    for v in (a,n):
        f=tuple(int(i==v) for i in range(n+1))
        key,d=term(-c,affine(lift(num)),n-4,[(affine(lift(g)),1) for g in den]+[(affine(f),1)])
        result[key]+=d
    return dict(result)

def catalog(n,fulltree,a):
    incident=[i for i,e in enumerate(fulltree) if a in e];states={}
    for bits in product((0,1),repeat=len(incident)):
        shifted=[];lookup=dict(zip(incident,bits))
        for i,(u,v) in enumerate(fulltree):
            if lookup.get(i):u=n if u==a else u;v=n if v==a else v
            shifted.append((u,v))
        shifted.append((a,n))
        for hi,headedge in enumerate(shifted):
            free=shifted[:hi]+shifted[hi+1:]
            for orientations in product((1,-1),repeat=n):
                u,v=headedge;head=[0]*(n+1);head[u]=orientations[0];head[v]=-orientations[0]
                edges=[(u,v) if sign==1 else (v,u) for (u,v),sign in zip(free,orientations[1:])]
                h,E=old.normalize(n+1,head,edges)
                atom=family.forest_atom(n+1,E,h);assert atom
                key,c=atom_term(n+1,atom)
                states.setdefault(key,(c,h,E))
    return states

def main():
    start=time.monotonic();n=4;head=(-1,1,0,0);edges=((1,2),(2,3));tree=((1,0),)+edges
    results=[];rng=random.Random(25102557)
    for a in (0,1,2,3):
        states=catalog(n,tree,a);keys=sorted(states);target=target_expression(n,head,edges,a)
        rows=[];points=[]
        while len(rows)<len(keys)+12:
            point=tuple(rng.randrange(1,15000) for _ in range(n))
            try:
                row=[family.eval_term(k,states[k][0],point) for k in keys]
                rhs=sum(family.eval_term(k,c,point) for k,c in target.items())%family.PRIME
            except ZeroDivisionError:continue
            rows.append(row+[rhs]);points.append(point)
        rr,rank=nmod_mat(rows,family.PRIME).rref()
        pivots=[next(j for j in range(len(keys)+1) if rr[i,j]) for i in range(rank)]
        gap=len(keys) in pivots;record=dict(split_label=a,columns=len(keys),ranks=[rank-int(gap),rank],
            status='MODULAR_LOCAL_VERTEX_SPLIT_GAP' if gap else 'MODULAR_LOCAL_VERTEX_SPLIT_INCLUSION')
        if not gap:
            solution=[Q(0)]*len(keys)
            for i,j in enumerate(pivots):solution[j]=old.reconstruct(int(rr[i,len(keys)]),family.PRIME)
            if all(c is not None for c in solution):
                residual=defaultdict(Q,{k:-c for k,c in target.items()})
                for k,c in zip(keys,solution):residual[k]+=c*states[k][0]
                V=Verifier(150);assert V.check(dict(residual))
                record.update(status='EXACT_LOCAL_VERTEX_SPLIT_IDENTITY',calls=V.calls,
                    selected=[dict(head=states[k][1],edges=states[k][2],coefficient=str(c)) for k,c in zip(keys,solution) if c])
        else:
            free=sorted(set(range(len(keys)))-set(pivots));kernels=[]
            for f in free:
                coefficients={f:Q(1)}
                for i,j in enumerate(pivots[:-1]):
                    c=old.reconstruct(int(-rr[i,f]),family.PRIME)
                    assert c is not None
                    if c:coefficients[j]=c
                residual=defaultdict(Q)
                for j,c in coefficients.items():residual[keys[j]]+=c*states[keys[j]][0]
                V=Verifier(150);assert V.check(dict(residual))
                kernels.append([[j,str(c)] for j,c in coefficients.items()])
            record.update(status='EXACT_LOCAL_VERTEX_SPLIT_OBSTRUCTION',kernels=kernels,
                          sources=[dict(head=states[k][1],edges=states[k][2]) for k in keys],points=points)
        results.append(record)
        result=dict(status='BOUNDED_VERTEX_SPLIT_RULE_GATE',old_labels=n,head=head,edges=edges,
            records=results,prime=family.PRIME,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            seconds=time.monotonic()-start,
            scope='Sources split one vertex of the full head-plus-hinge tree, add the split edge, and permit every head placement and orientation. This finite necessary gate is not a uniform closure theorem.')
        (HERE/'overnight_upper_baxter_vertex_split.json').write_text(json.dumps(result,indent=2)+'\n')
        print('VERTEX SPLIT',a,'COLS',len(keys),'RANKS',record['ranks'],record['status'],
              'SUPPORT',len(record.get('selected',[])),'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
