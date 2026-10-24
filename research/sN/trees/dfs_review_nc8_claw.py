#!/usr/bin/env python3
"""NC8 subdivided-claw extension, independently enumerated geometrically.
Choose the degree3 center, a perfect matching of the six remaining labels,
and the inner endpoint of each length2 arm. Keep noncrossing embeddings.
Orient away from an arbitrary source; the marked head root is arbitrary.
The source/root swap gives the same normalized function, so enumerate
unordered endpoint pairs including the diagonal. Output includes cut sums
and the exact D8 orbit partition, ready for Fourier column evaluation.
"""
import itertools,json,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
def matchings(xs):
 if not xs:yield [];return
 a=xs[0]
 for k in range(1,len(xs)):
  b=xs[k]
  for rest in matchings(xs[1:k]+xs[k+1:]):yield [(a,b)]+rest
def key(u,p=None):
 if p is None:p=list(range(8))
 h=[0]*8;h[p[u['root']]]=1;h[p[u['apex']]]=-1;es=[]
 for a,b in u['edges']:
  a,b=p[a],p[b]
  if a>b:h[a]+=1;h[b]-=1
  es.append(tuple(sorted((a,b))))
 return tuple(h),tuple(sorted(es))
start=time.time();trees=set()
for center in range(7):
 for pairs in matchings([i for i in range(7) if i!=center]):
  for bits in itertools.product((0,1),repeat=3):
   edges=[]
   for (x,y),b in zip(pairs,bits):
    inner,leaf=(x,y) if b else (y,x);edges.extend([(center,inner),(inner,leaf)])
   edges=tuple(sorted(tuple(sorted(e)) for e in edges))
   if any(a<c<b<d or c<a<d<b for a,b in edges for c,d in edges):continue
   trees.add(edges)
assert len(trees)==56
out={}
for es in sorted(trees):
 adj=[[] for _ in range(7)]
 for u,v in es:adj[u].append(v);adj[v].append(u)
 for s,r in itertools.combinations_with_replacement(range(7),2):
  seen={s};todo=[s];ori=[]
  while todo:
   u=todo.pop()
   for v in adj[u]:
    if v not in seen:seen.add(v);todo.append(v);ori.append((u,v))
  for apex in range(8):
   lab=[i for i in range(8) if i!=apex]
   unit=dict(apex=apex,source=lab[s],root=lab[r],edges=[(lab[u],lab[v]) for u,v in ori])
   cuts=[]
   for x,y in unit['edges']:
    aa={i:[] for i in lab}
    for u,v in unit['edges']:
     if (u,v)!=(x,y):aa[u].append(v);aa[v].append(u)
    side={x};todo=[x]
    while todo:
     for v in aa[todo.pop()]:
      if v not in side:side.add(v);todo.append(v)
    sg=1
    if unit['root'] in side:side=set(lab)-side;sg=-1
    cuts.append((sorted(side),sg))
   unit['cuts']=cuts;out[key(unit)]=unit
units=list(out.values());assert len(units)==12544
index={key(u):i for i,u in enumerate(units)};seen=set();orbits=[]
for i,u in enumerate(units):
 if i in seen:continue
 orb={index[key(u,[(sg*j+t)%8 for j in range(8)])] for sg in (-1,1) for t in range(8)}
 seen|=orb;orbits.append(sorted(orb))
assert len(seen)==len(units)
D=dict(n=8,shape='subdivided_claw',orientation='away_from_source',marked_root='arbitrary_including_source',
 status='EXACT_ENUMERATION',noncrossing_trees_per_apex=len(trees),units=units,orbits=orbits,
 diagonal_units=sum(u['root']==u['source'] for u in units),elapsed=time.time()-start)
(HERE/'dfs_review_nc8_claw.json').write_text(json.dumps(D,indent=2)+'\n')
print(json.dumps({k:(len(v) if k in ('units','orbits') else v) for k,v in D.items()},indent=2),flush=True)
