#!/usr/bin/env python3
r"""Exact exhaustive small-N validation of connected-germ root-head reduction.
Producer: python3 research/sN/trees/dfs_review_flow_check.py N
Enumerates all labelled trees on [N]\{0}, root 1, all five effective edge states
(omit, linear each way, hinge each way), all tie sets of size >=3, all outside
orders. Integer base B=N+2. Checks preactivation freezing, balance, and the
canonical-head conclusion for every connected surviving hinge germ.
This finite check supplements the general flow proof, not its replacement.
Budget N=5 (under one minute expected), no randomness.
"""
from itertools import product,combinations,permutations
import sys,json

def tree(seq,vs):
 deg={v:1 for v in vs}
 for v in seq:deg[v]+=1
 edges=[]
 for v in seq:
  u=min(u for u in vs if deg[u]==1)
  edges.append((u,v));deg[u]-=1;deg[v]-=1
 rest=[v for v in vs if deg[v]==1]
 edges.append(tuple(rest))
 return edges

def run(n):
 a=0;r=1;vs=list(range(1,n));B=n+2
 cases=zero=top=outside_root=0
 for seq in product(vs,repeat=n-3):
  edges=tree(seq,vs)
  for states in product(range(5),repeat=n-2):
   for m in range(3,n+1):
    for Tt in combinations(range(n),m):
     T=set(Tt);O=set(range(n))-T
     for order in permutations(O):
      p=[0]*n
      for q,i in enumerate(order):p[i]=-B**(m+q)
      b=[int(i==r)-int(i==a) for i in range(n)]
      pre=p[r]-p[a];H=[]
      for (i,j),s in zip(edges,states):
       if s==0:continue
       if s in (2,4):i,j=j,i
       d=p[i]-p[j]
       if s in (1,2):
        b[i]+=1;b[j]-=1;pre+=d
       elif i in T and j in T:H.append((i,j))
       else:
        pre+=max(d,0)
        if d>0:b[i]+=1;b[j]-=1
      cases+=1
      assert pre==sum(b[i]*p[i] for i in range(n))
      if pre:continue
      zero+=1
      assert all(b[i]==0 for i in O),(edges,states,Tt,order,b)
      assert a in T
      if len(H)!=m-2:continue
      # H is a forest, so m-2 edges on m-1 nonapex labels forces connectivity.
      top+=1;outside_root+=int(r not in T)
      roots=[i for i in T if b[i]==1]
      assert len(roots)==1 and roots[0]!=a
      rr=roots[0]
      assert b==[int(i==rr)-int(i==a) for i in range(n)],(edges,states,Tt,order,b)
      # Canonical root = first vertex in T along the original root-to-T path.
      if r in T:assert rr==r
      else:
       comp={r};change=True
       while change:
        change=False
        for i,j in edges:
         if i in O and j in O and ((i in comp)!=(j in comp)):
          comp|={i,j};change=True
       attach={j if i in comp else i for i,j in edges if ((i in comp)!=(j in comp))}
       assert attach=={rr},(edges,states,Tt,order,b,comp,attach)
 return dict(N=n,base=B,cases=cases,zero_preactivations=zero,connected_germs=top,root_outside=outside_root,status='ALL_EXACT_CHECKS_PASS')
print(json.dumps(run(int(sys.argv[1])),indent=2))
