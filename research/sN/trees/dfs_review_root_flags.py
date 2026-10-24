#!/usr/bin/env python3
"""Exact-integer evaluation/modular-rank diagnostic of root-head tree flag vectors.
Producer: python3 research/sN/trees/dfs_review_root_flags.py M [mode]
Domain: all labelled rooted oriented trees on [M] minus the apex, hinge states only.
Mode nopath/default filters to underlying nonpaths. Sampled rank equality does NOT certify
functional span; modular rank increase is only a separation diagnostic until checked over the rationals.
Budget: M=5 first (<1 min), M=6 only if informative. No random choices.
"""
import sys, itertools
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from pn_test import forests,is_ham_path,is_spanning,rank_mod_p
from flag_test import pyramid,orders,tau_vector
import numpy as np
m=int(sys.argv[1]); mode=sys.argv[2] if len(sys.argv)>2 else 'nopath'
ords=orders(m); rows=[]; units=[]
for a in range(m):
 vs=[i for i in range(m) if i!=a]
 for F in forests(vs):
  if not is_spanning(F,vs) or (mode=='nopath' and is_ham_path(F,vs)):continue
  for root in vs:
   v=[int(i==root)-int(i==a) for i in range(m)]
   for bits in itertools.product((0,1),repeat=len(F)):
    oriented=[edge if bit else edge[::-1] for edge,bit in zip(F,bits)]
    rows.append(tau_vector(m,pyramid(m,v,oriented),ords))
    units.append(dict(apex=a,root=root,edges=oriented))
A=np.array(rows,dtype=np.int64).T
B=np.ones((len(ords),1),dtype=np.int64)
r=rank_mod_p(A);r1=rank_mod_p(np.concatenate((A,B),axis=1))
print(dict(m=m,mode=mode,units=len(rows),flags=len(ords),rank=r,with_max=r1,separated=r1>r),flush=True)

if m==5:
 from fractions import Fraction
 from pn_test import P
 import sympy as sp, json
 R=A.copy()%P; rr=0; piv=[]
 for c in range(R.shape[1]):
  nz=np.flatnonzero(R[rr:,c])
  if not len(nz):continue
  j=rr+int(nz[0]);R[[rr,j]]=R[[j,rr]]
  R[rr]=(R[rr]*pow(int(R[rr,c]),P-2,P))%P
  col=R[:,c].copy();col[rr]=0
  R=(R-col[:,None]*R[rr][None,:])%P
  piv.append(c);rr+=1
  if rr==len(R):break
 C=sp.Matrix(A[:,piv].tolist());target=sp.ones(len(ords),1)
 sol,params=C.gauss_jordan_solve(target)
 assert not list(params)
 assert C*sol==target
 witness=[dict(unit=units[j],coefficient=str(sol[k])) for k,j in enumerate(piv) if sol[k]]
 print(json.dumps(dict(exact_coordinate_flag_identity=True,nonzero_terms=len(witness),witness=witness),indent=2))
