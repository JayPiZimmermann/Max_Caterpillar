#!/usr/bin/env python3
"""Independent audit of the six-label one-descent Fourier obstruction.
Regenerate the dictionary, recompute graph cuts, check all stored evaluations,
recompute both modular ranks, and verify the six sparse rational identities
by a separately constructed common denominator over Q[z0,...,z4].
"""
import sys,json,math,time
from pathlib import Path
from collections import Counter
import numpy as np
import sympy as sp
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'all_tree_dfs'))
from upper_fourier import family
start=time.time();D=json.loads((HERE/'all_tree_dfs/upper_fourier_6_desc1.json').read_text());C=json.loads((HERE/'all_tree_dfs/upper_rank_certificate_6_desc1.json').read_text())
n=6;P=D['prime'];units=family(n,1);assert units==D['units'] or json.loads(json.dumps(units))==D['units']
def cuts(u):
 out=[]
 for x,y in u['edges']:
  adj={i:[] for i in range(n) if i!=u['apex']}
  for v,w in u['edges']:
   if (v,w)==(x,y):continue
   adj[v].append(w);adj[w].append(v)
  side={x};todo=[x]
  while todo:
   for v in adj[todo.pop()]:
    if v not in side:side.add(v);todo.append(v)
  sg=1
  if u['root'] in side:side=set(adj)-side;sg=-1
  out.append((sorted(side),sg))
 return out
cc=[cuts(u) for u in units]
assert cc==[[(side,s) for side,s in u['cuts']] for u in D['units']]
def rank(rows):
 b={}
 for row in rows:
  v=np.array(row,dtype=np.int64)%P
  for j,w in sorted(b.items()):v=(v-v[j]*w)%P
  nz=np.flatnonzero(v)
  if len(nz):j=int(nz[0]);b[j]=v*pow(int(v[j]),P-2,P)%P
 return len(b)
rows=[]
for pt,saved in zip(D['points'],D['rows']):
 row=[]
 for u,es in zip(units,cc):
  a=pt[u['apex']];den=math.prod(sum(pt[i] for i in side)*(sum(pt[i] for i in side)+s*a) for side,s in es)
  row.append(pow(-a,n-4,P)*pow(den%P,P-2,P)%P)
 row.append(-pow(math.prod(pt)%P,P-2,P)%P);assert row==saved;rows.append(row)
ranks=[rank([r[:-1] for r in rows]),rank(rows)]
z=sp.symbols('z:5');om=list(z)+[-sum(z)];parts=[]
for u,es in zip(units,cc):
 a=om[u['apex']];fc=Counter();sg=1
 for side,s in es:
  q=sum(om[i] for i in side)
  for f in (q,q+s*a):
   p=sp.Poly(f,*z);co=tuple(p.coeff_monomial(v) for v in z)
   v=next(x for x in co if x)
   if v<0:sg=-sg;co=tuple(-x for x in co)
   fc[co]+=1
 parts.append((sp.Poly(sg*(-a)**2,*z),fc))
rels=C['exact_relations'];M=sp.zeros(len(rels),len(units));identities=[]
for k,rel in enumerate(rels):
 common=Counter()
 for j,c in rel:common|=parts[j][1];M[k,j]=c
 val=sp.Poly(0,*z)
 for j,c in rel:
  num=c*parts[j][0]
  for f,power in (common-parts[j][1]).items():num*=sp.Poly(sum(v*t for v,t in zip(f,z)),*z)**power
  val+=num
 identities.append(val.is_zero)
out=dict(status='EXACT_OBSTRUCTION_RECHECK_PASS' if ranks==[711,712] and all(identities) and M.rank()==6 else 'FAIL',columns=len(units),rows=len(rows),modular_ranks=ranks,independent_exact_relations=M.rank(),identities=identities,elapsed=time.time()-start)
print(json.dumps(out,indent=2),flush=True);(HERE/'dfs_review_upper_obstruction_6.json').write_text(json.dumps(out,indent=2)+'\n')
