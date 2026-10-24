#!/usr/bin/env python3
"""Exact semantic controls for the continuation, budget 30 seconds.
Part A exhausts all labelled N=7 full-hinge trees and ordered source/root
pairs, computes normalized kappa and the existing heir cover, and checks
the sharper degree2 statement. Part B exhausts all N=5 TreeFace states,
ties, and outside orders to test leaf forcing and conditional pair rules.
No randomness, floating arithmetic, or edited production Lean files.
"""
import itertools,json,time
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent;start=time.time();BUDGET=30
def tree(seq,vs):
 deg={v:1 for v in vs}
 for v in seq:deg[v]+=1
 es=[]
 for v in seq:
  u=min(w for w in vs if deg[w]==1);es.append((u,v));deg[u]-=1;deg[v]-=1
 es.append(tuple(v for v in vs if deg[v]==1));return es
def rooted(adj,r):
 par={r:None};todo=[r]
 while todo:
  u=todo.pop()
  for v in adj[u]:
   if v not in par:par[v]=u;todo.append(v)
 return par
count=0;maxomega=0;witness=None
n=7;vs=list(range(1,n))
for seq in itertools.product(vs,repeat=n-3):
 es=tree(seq,vs);adj={v:set() for v in vs}
 for u,v in es:adj[u].add(v);adj[v].add(u)
 for s,r in itertools.product(vs,repeat=2):
  ps=rooted(adj,s);pr=rooted(adj,r);ori=[(p,v) for v,p in ps.items() if p is not None]
  h=[int(v==r)-int(v==0) for v in range(n)]
  for u,v in ori:
   if u>v:h[u]+=1;h[v]-=1
  kap=[h[v]+sum(v==min(e) for e in es) for v in range(n)]
  assert all(kap[v]==len(adj[v])-1+int(v==s)+int(v==r) for v in vs)
  pend={v for v in vs if len(adj[v])==1 and kap[v]==0}
  out={v for v in vs if len(adj[v])==1 and kap[v]==1}
  fixed={v for v in vs if len(adj[v])==1 and kap[v] not in (0,1)}
  poor={v for v in vs if len(adj[v])>1 and not adj[v]&(pend|out)}
  R={v:set() for v in vs}
  for v in out:
   w=next(iter(adj[v]))
   if w not in pend:R[v].add(w);R[w].add(v)
  for v in poor:
   child=[w for w in adj[v] if pr[w]==v];assert child
   w=min(child);R[v].add(w);R[w].add(v)
  assert all(len(R[v])<=2 for v in vs)
  assert all(v in pend or R[v] or adj[v]&pend or v in fixed for v in vs)
  om=max(len(adj[v]&out)+int(any(len(adj[w])>1 for w in adj[v])) for v in vs)
  if om>maxomega:maxomega=om;witness=dict(edges=es,source=s,root=r,kappa=kap,cover={v:sorted(R[v]) for v in vs})
  count+=1
 if time.time()-start>BUDGET:raise TimeoutError('declared budget')
A=dict(N=n,units=count,max_omega=maxomega,max_cover_degree=2,omega3_witness=witness)
n=5;a=0;r=1;vs=list(range(1,n));base=n+2;cases=top=good=pairtests=0
for seq in itertools.product(vs,repeat=n-3):
 es=tree(seq,vs);adj={v:set() for v in vs}
 for u,v in es:adj[u].add(v);adj[v].add(u)
 leaves=[v for v in vs if len(adj[v])==1 and v!=r]
 for states in itertools.product(range(5),repeat=n-2):
  typ={};ori=[]
  for (u,v),st in zip(es,states):
   if st in (2,4):u,v=v,u
   ori.append((u,v))
   for leaf in leaves:
    if leaf in (u,v):typ[leaf]='omit' if st==0 else 'linear' if st<3 else 'out' if u==leaf else 'in'
  for m in range(3,n+1):
   for tt in itertools.combinations(range(n),m):
    T=set(tt);O=set(range(n))-T
    for order in itertools.permutations(O):
     p=[0]*n
     for q,v in enumerate(order):p[v]=-base**(m+q)
     h=[int(v==r)-int(v==a) for v in range(n)];pre=p[r]-p[a];H=[]
     for (u,v),st in zip(ori,states):
      if not st:continue
      z=p[u]-p[v]
      if st<3:pre+=z;h[u]+=1;h[v]-=1
      elif u in T and v in T:H.append((u,v))
      elif z>0:pre+=z;h[u]+=1;h[v]-=1
     cases+=1
     if pre or len(H)!=m-2:continue
     top+=1;rr=next(v for v in T if h[v]==1)
     hd=Counter(v for e in H for v in e);outs=Counter(v for u,v in H if hd[u]==1 and u!=rr)
     for leaf in leaves:
      hub=next(iter(adj[leaf]));t=typ[leaf]
      assert t!='linear'
      if t=='omit':assert leaf not in T
      if t=='in':assert (leaf in T)==(hub in T)
      if t=='out' and leaf in T:assert hub in T
     if any(c>=2 for c in outs.values()):continue
     good+=1
     for x,y in itertools.combinations(leaves,2):
      if adj[x]!=adj[y]:continue
      tx,ty=typ[x],typ[y];bx,by=x in T,y in T
      if tx==ty=='out':assert not(bx and by)
      elif tx==ty=='in':assert bx==by
      elif tx=='in' and ty=='out':assert not(by and not bx)
      elif tx=='out' and ty=='in':assert not(bx and not by)
      elif tx=='omit' or ty=='omit':assert not bx if tx=='omit' else not by
      else:raise AssertionError('unexpected state')
      pairtests+=1
B=dict(N=n,configurations=cases,connected_top_germs=top,no_out_twin_germs=good,leaf_pair_checks=pairtests)
assert time.time()-start<BUDGET
out=dict(status='EXACT_CONTINUATION_CHECKS_PASS',budget_seconds=BUDGET,cover=A,leaf_pairs=B,elapsed=time.time()-start)
print(json.dumps(out,indent=2));(HERE/'dfs_review_continue_checks.json').write_text(json.dumps(out,indent=2)+'\n')
