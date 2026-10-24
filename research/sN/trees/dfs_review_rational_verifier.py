#!/usr/bin/env python3
"""Independent controls for recursive exact rational-identity verification.
Generate affine partial-fraction identities and repeated derivatives, and
affine binomial quotient identities; verify each true identity and reject
its perturbation by a nonzero constant. No numerical evaluations used.
"""
import sys,random,json,time,math
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import add,Verifier
rng=random.Random(271024);start=time.time();checks=0
def check(e,d):
 global checks
 assert Verifier(10).check(e)
 add(e,Q(7,13),(0,)*d+(1,),0,[])
 assert not Verifier(10).check(e)
 checks+=2
def derivative(e,j):
 out=defaultdict(Q)
 for (num,k,den),c in e.items():
  if k and num[j]:add(out,c*k*num[j],num,k-1,den)
  for f,p in den:
   if f[j]:add(out,-c*p*f[j],num,k,[(g,q+int(g==f)) for g,q in den])
 return out
for d in (1,2,3):
 for trial in range(8):
  f=tuple(rng.randint(-3,3) for _ in range(d+1));g=tuple(rng.randint(-3,3) for _ in range(d+1))
  if not any(f) or not any(g) or not any(a+b for a,b in zip(f,g)):continue
  s=tuple(a+b for a,b in zip(f,g));one=(0,)*d+(1,)
  e=defaultdict(Q)
  add(e,1,one,0,[(f,1),(g,1)])
  add(e,-1,one,0,[(f,1),(s,1)])
  add(e,-1,one,0,[(g,1),(s,1)])
  for _ in range(trial%3):e=derivative(e,rng.randrange(d))
  check(e,d)
  k=2+trial%3;e=defaultdict(Q);add(e,1,s,k,[(f,k)])
  for j in range(k+1):add(e,-math.comb(k,j),g,j,[(f,j)] if j else [])
  check(e,d)
out=dict(status='EXACT_SYMBOLIC_CONTROLS_PASS',checks=checks,dimensions=[1,2,3],elapsed=time.time()-start)
print(json.dumps(out,indent=2));(HERE/'dfs_review_rational_verifier.json').write_text(json.dumps(out,indent=2)+'\n')
