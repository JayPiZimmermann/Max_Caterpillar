#!/usr/bin/env python3
"""Budgeted modular diagnostic only; no rational result is claimed.
Use vectorized lookup inversion at a million-sized prime. Maximum run time
110 seconds; maximum evaluated rows can be specified. Rooted oriented orbit
enumeration is shared with the exact rational producer.
"""
import sys,time,json,itertools,math
from pathlib import Path
import numpy as np
from dfs_review_fourier import family,points
P=1000003
HERE=Path(__file__).resolve().parent

def main():
 m=int(sys.argv[1]);mode=sys.argv[2];count=int(sys.argv[3]);start=time.time()
 fam=family(m,mode);perms=np.array(list(itertools.permutations(range(m))),dtype=np.int64)
 print('domain',m,mode,'orbits',len(fam),'budget_sec',110,flush=True)
 inv=np.zeros(P,dtype=np.int64);inv[1]=1
 for j in range(2,P):inv[j]=P-(P//j)*inv[P%j]%P
 cuts=[[(sum(1<<i for i in side),sgn) for side,sgn in u['cuts']] for u in fam]
 needed=sorted(set(mask for es in cuts for mask,sgn in es))
 basisA={};basisB={};rows=[];pts=[]
 def insert(row,basis):
  v=np.array(row,dtype=np.int64)%P
  for j,b in sorted(basis.items()):v=(v-v[j]*b)%P
  nz=np.flatnonzero(v)
  if len(nz):
   j=int(nz[0]);basis[j]=v*inv[v[j]]%P
 for pt in points(m,count*2):
  om=np.array(pt,dtype=np.int64)[perms]%P;a=om[:,0]
  Q={mask:om[:,[i for i in range(m) if mask>>i&1]].sum(axis=1)%P for mask in needed}
  numer=np.ones(len(perms),dtype=np.int64)
  for _ in range(m-4):numer=numer*(-a)%P
  row=[];ok=True
  for es in cuts:
   den=np.ones(len(perms),dtype=np.int64)
   for mask,sgn in es:
    q=Q[mask];den=den*q%P;den=den*((q+sgn*a)%P)%P
   if np.any(den==0):ok=False;break
   row.append(int((numer*inv[den]%P).sum()%P))
  if not ok:continue
  tar=int(inv[math.prod(pt)%P]);insert(row,basisA);insert(row+[tar],basisB)
  rows.append(row+[tar]);pts.append(pt)
  if len(rows)%10==0:print('rows',len(rows),'ranks',len(basisA),len(basisB),'elapsed',round(time.time()-start,2),flush=True)
  if len(rows)>=count or time.time()-start>=110:break
 data=dict(m=m,mode=mode,orbits=len(fam),prime=P,rows=len(rows),modular_ranks=[len(basisA),len(basisB)],elapsed=time.time()-start,status='MODULAR_DIAGNOSTIC_ONLY',points=pts,evaluations=rows)
 (HERE/f'dfs_review_fourier_fast_{m}_{mode}.json').write_text(json.dumps(data,indent=2)+'\n')
 print('DONE', {k:v for k,v in data.items() if k not in ('points','evaluations')},flush=True)
if __name__=='__main__':main()
