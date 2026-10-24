#!/usr/bin/env python3
"""Fourier rational-function separation for canonical-root nonpath tree germs.
Producer: OPENBLAS_NUM_THREADS=1 research/sN/dfs/h4-general-neurons/venv/bin/python this.py m mode samples
mode: nopath or twin. Uses all unlabeled shapes satisfying the filter, every root and
orientation modulo graph automorphisms, all m! label permutations. Integer frequencies
have m-1 positive superincreasing entries and one negative sum, excluding every pole.
A finite-field proposal chooses test rows. An exact rational separator, verified against
ALL orbit columns and the target, is the only promoted positive outcome.
"""
import sys,itertools,json,time,random,math
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import networkx as nx
import sympy as sp
import numpy as np
P=2147483629
HERE=Path(__file__).resolve().parent

def family(m,mode):
 out=[]
 for G in nx.nonisomorphic_trees(m-1):
  G=nx.convert_node_labels_to_integers(G,first_label=1)
  E=tuple(sorted(tuple(sorted(e)) for e in G.edges()))
  if mode=='nopath' and max(dict(G.degree()).values())<=2:continue
  autos=list(nx.algorithms.isomorphism.GraphMatcher(G,G).isomorphisms_iter())
  seen=set()
  for root in G:
   for bits in itertools.product((0,1),repeat=len(E)):
    ori=tuple((u,v) if b else (v,u) for (u,v),b in zip(E,bits))
    if mode=='twin':
     sig={}
     for leaf in G:
      if G.degree(leaf)!=1 or leaf==root:continue
      cen=next(iter(G.neighbors(leaf)))
      direction=int((leaf,cen) in ori)
      sig[(cen,direction)]=sig.get((cen,direction),0)+1
     if not any(v>=2 for v in sig.values()):continue
    key=min((a[root],tuple(sorted((a[u],a[v]) for u,v in ori))) for a in autos)
    if key in seen:continue
    seen.add(key)
    cuts=[]
    for u,v in ori:
     GG=G.copy();GG.remove_edge(u,v)
     side=nx.node_connected_component(GG,u)
     if root in side:side=set(G)-side;sgn=-1
     else:sgn=1
     cuts.append((tuple(sorted(side)),sgn))
    out.append(dict(root=root,edges=ori,cuts=cuts))
 return out

def points(m,count):
 rng=random.Random(1729);seen=set()
 # keep small poles to limit denominator growth in the exact orbit sums.
 for seed in range(2,12):
  pos=[seed**i for i in range(m-1)];key=tuple([-sum(pos)]+pos)
  if key not in seen:seen.add(key);yield key
  if len(seen)>=count:return
 while len(seen)<count:
  pos=[rng.randint(1,5)]
  for _ in range(m-2):pos.append(sum(pos)+rng.randint(1,10))
  key=tuple([-sum(pos)]+pos)
  if key not in seen:seen.add(key);yield key

def orbit_mod(unit,pt,m,perms):
 total=0
 for p in perms:
  om=[pt[i] for i in p];a=om[0];den=1
  for side,sgn in unit['cuts']:
   q=sum(om[i] for i in side);den=den*q*(q+sgn*a)%P
  if not den:raise ValueError('pole')
  total=(total+pow((-a)%P,m-4,P)*pow(den,P-2,P))%P
 return total

def orbit_exact(unit,pt,m,perms):
 total=Fraction(0)
 for p in perms:
  om=[pt[i] for i in p];a=om[0];den=1
  for side,sgn in unit['cuts']:
   q=sum(om[i] for i in side);den*=q*(q+sgn*a)
  assert den
  total+=Fraction((-a)**(m-4),den)
 return total

def row_pivots(rows):
 basis={};piv=[]
 for i,row in enumerate(rows):
  v=np.array(row,dtype=np.int64)%P
  for j,b in sorted(basis.items()):v=(v-v[j]*b)%P
  nz=np.flatnonzero(v)
  if len(nz):
   j=int(nz[0]);v=v*pow(int(v[j]),P-2,P)%P;basis[j]=v;piv.append(i)
 return piv

def main():
 m=int(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'nopath';npts=int(sys.argv[3]) if len(sys.argv)>3 else 35
 start=time.time();fam=family(m,mode);perms=list(itertools.permutations(range(m)));pts=list(points(m,npts))
 print('domain',m,mode,'orbits',len(fam),'points',npts,flush=True)
 rows=[]
 for i,pt in enumerate(pts):
  row=[orbit_mod(u,pt,m,perms) for u in fam]
  target=pow(math.prod(pt)%P,P-2,P)
  rows.append(row+[target])
  if i%5==0:print('row',i,'elapsed',round(time.time()-start,2),flush=True)
 pA=row_pivots([r[:-1] for r in rows]);pAb=row_pivots(rows)
 data=dict(m=m,mode=mode,orbits=len(fam),modular_ranks=[len(pA),len(pAb)],points=pts,representatives=fam)
 print('modular ranks',data['modular_ranks'],flush=True)
 if len(pAb)<=len(pA):
  data['status']='NO_SEPARATION_IN_TESTED_ROWS'
 else:
  psel=pAb;R=[]
  for idx in psel:
   pt=pts[idx];R.append([sp.Rational(orbit_exact(u,pt,m,perms)) for u in fam]+[sp.Rational(1,math.prod(pt))])
   print('exact row',idx,'elapsed',round(time.time()-start,2),flush=True)
  M=sp.Matrix(R);print('exact nullspace starting',M.shape,flush=True)
  for v in M[:,:-1].T.nullspace():
   q=(v.T*M[:,-1])[0]
   if q:
    v=v/q
    assert v.T*M[:,:-1]==sp.zeros(1,len(fam));assert (v.T*M[:,-1])[0]==1
    data['status']='EXACT_RATIONAL_SEPARATOR';data['separator']=dict(point_indices=psel,weights=[str(x) for x in v]);data['exact_rows']=[[str(x) for x in row] for row in R]
    print('EXACT_SEPARATOR',len(psel),'rows','elapsed',round(time.time()-start,2),flush=True);break
  else:data['status']='MODULAR_PROPOSAL_FAILED_OVER_Q'
 (HERE/f'dfs_review_fourier_{m}_{mode}.json').write_text(json.dumps(data,indent=2)+'\n')
 print('DONE',data['status'],flush=True)
if __name__=='__main__':main()
