#!/usr/bin/env python3
"""Independent NC8 coverage via Prüfer trees and source/root paths.
Read only dictionary/orbit metadata, never the 4k-by-4k evaluation matrix.
Original caterpillar descriptions are equivalent to rooted out-arborescences
whose source--marked-root path contains every nonleaf vertex. Reversing the
path and exchanging its endpoints gives the same normalized function.
"""
import sys,json,itertools,time,heapq,gzip
from pathlib import Path
HERE=Path(__file__).resolve().parent
def header(path):
 lines=[]
 with (path.open() if path.exists() else gzip.open(str(path)+'.gz','rt')) as f:
  for line in f:
   if line.startswith('  "points":'):break
   lines.append(line)
 return json.loads(''.join(lines)+'  "points": []\n}\n')
def tree(seq,n):
 deg=[1]*n
 for i in seq:deg[i]+=1
 leaves=[i for i,d in enumerate(deg) if d==1];heapq.heapify(leaves);es=[]
 for j in seq:
  i=heapq.heappop(leaves);es.append((i,j));deg[i]-=1;deg[j]-=1
  if deg[j]==1:heapq.heappush(leaves,j)
 es.append(tuple(leaves));return es
def key(a,r,es,n):
 h=[0]*n;h[r]=1;h[a]=-1
 for u,v in es:
  if u>v:h[u]+=1;h[v]-=1
 return tuple(h),tuple(sorted(tuple(sorted(e)) for e in es))
start=time.time();n=8;D=header(HERE/'all_tree_dfs/nc_fast_8.json')
saved={key(u['apex'],u['root'],u['edges'],n) for u in D['units']}
assert len(saved)==len(D['units'])
assert sorted(i for o in D['orbits'] for i in o)==list(range(len(saved)))
# Check every stored orbit is exactly its dihedral orbit in normalized keys.
for orb in D['orbits']:
 u=D['units'][orb[0]];expected=set()
 for s in (-1,1):
  for t in range(n):
   p=[(s*j+t)%n for j in range(n)]
   expected.add(key(p[u['apex']],p[u['root']],[(p[x],p[y]) for x,y in u['edges']],n))
 assert expected=={key(D['units'][i]['apex'],D['units'][i]['root'],D['units'][i]['edges'],n) for i in orb}
got=set();newshape={};nc_trees=nc_cats=nc_noncat=0
for seq in itertools.product(range(n-1),repeat=n-3):
 es=tree(seq,n-1);ee=[sorted(e) for e in es]
 if any(a<c<b<d or c<a<d<b for a,b in ee for c,d in ee):continue
 nc_trees+=1;adj=[[] for _ in range(n-1)]
 for u,v in es:adj[u].append(v);adj[v].append(u)
 core={i for i in range(n-1) if len(adj[i])>1}
 cat=all(sum(j in core for j in adj[i])<=2 for i in core)
 nc_cats+=cat;nc_noncat+=not cat
 if not cat:assert sorted(map(len,adj))==[1,1,1,2,2,2,3]
 for s,r in itertools.combinations(range(n-1),2):
  parents={s:None};todo=[s];ori=[]
  while todo:
   u=todo.pop()
   for v in adj[u]:
    if v not in parents:parents[v]=u;todo.append(v);ori.append((u,v))
  path=set();v=r
  while v is not None:path.add(v);v=parents[v]
  covered=core<=path
  if cat and not covered:continue
  for a in range(n):
   labels=[i for i in range(n) if i!=a];edges=[(labels[u],labels[v]) for u,v in ori]
   k=key(a,labels[r],edges,n)
   if covered:got.add(k)
   elif not cat:newshape[k]=dict(apex=a,root=labels[r],source=labels[s],edges=edges)
out=dict(status='EXACT_NC8_COVERAGE_PASS' if got==saved else 'COVERAGE_MISMATCH',
 saved_units=len(saved),independent_units=len(got),missing=len(got-saved),extra=len(saved-got),
 dihedral_orbits=len(D['orbits']),noncrossing_trees_on_7=nc_trees,
 noncrossing_caterpillars_on_7=nc_cats,noncrossing_subdivided_claws_on_7=nc_noncat,
 newshape_out_arborescence_units=len(newshape),elapsed=time.time()-start)
print(json.dumps(out,indent=2),flush=True)
(HERE/'dfs_review_nc8_coverage.json').write_text(json.dumps(out,indent=2)+'\n')
(HERE/'dfs_review_nc8_newshape.json').write_text(json.dumps(dict(n=8,units=list(newshape.values())),indent=2)+'\n')
