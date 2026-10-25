#!/usr/bin/env python3
"""Exact remaining coordinate-pole constant after four signed leaf deletions."""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import hashlib,json,time
from overnight_uniform_endpoint_q2_coordinate import key
HERE=Path(__file__).parent
started=time.monotonic()
units=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text())['units']
p=json.loads((HERE/'overnight_uniform_endpoint_q2.json').read_text())['results'][1]['proposals'][0]
state=[(int(c),units[int(i)]['root'],list(map(tuple,units[int(i)]['edges'])))for i,c in p['integer_proposal'].items()]
stages=[]
for N in (9,8,7,6):
    groups=Counter(); reps={}
    for weight,root,edges0 in state:
        edges=list(edges0);degree=Counter(v for e in edges for v in e)
        if degree[root]==1:
            neighbor=next(v if w==root else w for w,v in edges if root in(w,v))
            assert (neighbor,root)in edges,(N,root,edges)
            edges.remove((neighbor,root));edges.append((root,neighbor));root=neighbor
        assert degree[root]>1
        for leaf in degree:
            if degree[leaf]!=1:continue
            edge=next(e for e in edges if leaf in e)
            epsilon=1 if edge[0]==leaf else -1
            reduced=[e for e in edges if e!=edge]
            k=key(root,reduced);groups[k]-=weight*epsilon;reps[k]=(root,reduced)
    state=[(c,*reps[k])for k,c in groups.items()if c]
    stages.append(dict(arity_after=N-1,surviving_classes=len(state)))
freq=(-40,1,3,9,27);assert sum(freq)==0
value=Fraction(0);summands=0
for weight,root,edges in state:
    verts=sorted({v for e in edges for v in e});assert len(verts)==4
    adj={v:[]for v in verts}
    for x,y in edges:adj[x].append(y);adj[y].append(x)
    cuts=[]
    def dfs(v,parent):
        subtree={v}
        for w in adj[v]:
            if w==parent:continue
            child=dfs(w,v);eps=1 if(w,v)in edges else -1
            cuts.append((child,eps));subtree|=child
        return subtree
    dfs(root,None)
    for perm in permutations(freq):
        a=perm[0];omega=dict(zip(verts,perm[1:]));den=1
        for subset,eps in cuts:
            q=sum(omega[v]for v in subset)
            assert q and q+eps*a,(a,omega,subset,eps)
            den*=q*(q+eps*a)
        value+=weight*Fraction(-a,den);summands+=1
prod=1
for x in freq:prod*=x
c=value*prod
out=dict(status='EXACT_COORDINATE_CONSTANT_CHECK',stages=stages,frequency=freq,summands=summands,value=str(value),constant=str(c),zero=c==0,
 scope='Assuming all noncoordinate poles vanish, the original homogeneous degree -9 full symmetric rational relation is c/product(omega). Four coordinate residues preserve c; their N5 value is computed exactly here. The leaf-deletion and pole-completeness bridges still require independent semantic review.',
 producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
