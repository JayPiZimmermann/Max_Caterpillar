#!/usr/bin/env python3
"""Rebuild the NC7 rational identity from graph edges and saved coefficients.
Checks graph validity, noncrossing, the orbit partition, and every used cut.
Then invokes the independently audited exact principal-part verifier.
"""
import sys,json,time
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import Verifier,add
start=time.time();D=json.loads((HERE/'all_tree_dfs/nc_fast_7.json').read_text());n=7
units=D['units'];orbits=D['orbits'];cs=list(map(Q,D['coefficient_proposal']))
assert sorted(i for orb in orbits for i in orb)==list(range(len(units)))
fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
expr=defaultdict(Q);used=0
for c,orb in zip(cs,orbits):
 if not c:continue
 for idx in orb:
  u=units[idx];a=u['apex'];r=u['root'];es=[tuple(e) for e in u['edges']]
  assert r!=a and len(es)==n-2 and len(set(frozenset(e) for e in es))==n-2
  ee=[sorted(e) for e in es]
  assert not any(i<k<j<l or k<i<l<j for i,j in ee for k,l in ee)
  den=[];computed=[]
  for x,y in es:
   adj={i:[] for i in range(n) if i!=a}
   for v,w in es:
    assert v in adj and w in adj
    if (v,w)!=(x,y):adj[v].append(w);adj[w].append(v)
   side={x};todo=[x]
   while todo:
    for v in adj[todo.pop()]:
     if v not in side:side.add(v);todo.append(v)
   assert y not in side
   sg=1
   if r in side:side=set(adj)-side;sg=-1
   computed.append((sorted(side),sg))
   q=tuple(sum(fs[i][j] for i in side) for j in range(n))
   den.extend([(q,1),(tuple(x+sg*y for x,y in zip(q,fs[a])),1)])
  assert computed==[(side,sg) for side,sg in u['cuts']]
  add(expr,c,tuple(-x for x in fs[a]),n-4,den);used+=1
add(expr,-1,(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
V=Verifier(150);ok=V.check(expr)
out=dict(status='EXACT_NC7_IDENTITY_RECHECK_PASS' if ok else 'FAIL',support_units=used,normalized_terms=len(expr),calls=V.calls,elapsed=time.time()-start)
print(json.dumps(out,indent=2));(HERE/'dfs_review_nc7_identity.json').write_text(json.dumps(out,indent=2)+'\n')
