#!/usr/bin/env python3
"""Independent check of complete_flags_5 separator using only vertex maxima/minima.
Uses the saved six subspace chains/weights, reconstructs their fixed directions,
then evaluates every labelled rooted oriented 4-vertex star (640 units) by direct
successive exposed-face operations. It does not call pyramid's recursive invariant.
The separator is symmetrised over all 120 coordinate permutations, because the
producer matrix used orbit sums; target is normalised accordingly.
Producer: research/sN/dfs/h4-general-neurons/venv/bin/python this_file.py
"""
import sys,json,itertools,math
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import sympy as sp
folder=Path(__file__).resolve().parent
D=json.loads((folder/'all_tree_dfs/complete_flags_5.json').read_text())
keys=sp.sympify(D['keys']);m=D['m'];coeff=list(map(Fraction,D['separator']['weights']))
H=sp.Matrix([[int(i==j)-int(i==m-1) for i in range(m)] for j in range(m-1)])
flags=[]
for row in D['separator']['rows']:
 chain=keys[row];W=H;dirs=[]
 for V in chain:
  B=sp.Matrix(V);ns=(B*W.T).nullspace();assert len(ns)==1
  u=list(W.T*ns[0]);c=next(x for x in u if x);u=[x/c for x in u]
  den=sp.ilcm(*[sp.denom(x) for x in u]);dirs.append(tuple(int(den*x) for x in u));W=B
 last=chain[-1][0];j=next(i for i,x in enumerate(last) if x)
 flags.append((tuple(dirs),j))

def eval_flag(verts,dirs,j):
 if not dirs:
  vv=[p[j] for p in verts];return max(vv)-min(vv)
 u=dirs[0];vs=[sum(x*y for x,y in zip(p,u)) for p in verts];hi=max(vs);lo=min(vs)
 return eval_flag(tuple(p for p,q in zip(verts,vs) if q==hi),dirs[1:],j)-eval_flag(tuple(p for p,q in zip(verts,vs) if q==lo),dirs[1:],j)

def pyramid(a,r,edges):
 out={tuple([0]*m)}
 for bits in itertools.product((0,1),repeat=len(edges)):
  x=[int(i==r)-int(i==a) for i in range(m)]
  for bit,(i,j) in zip(bits,edges):
   if bit:x[i]+=1;x[j]-=1
  out.add(tuple(x))
 return tuple(sorted(out))

def f(verts):return sum(c*eval_flag(verts,U,j) for c,(U,j) in zip(coeff,flags))
perms=list(itertools.permutations(range(m)))
@lru_cache(None)
def sym(verts):return sum(f(tuple(tuple(v[i] for i in p) for v in verts)) for p in perms)
count=0
for a in range(m):
 for c in range(m):
  if c==a:continue
  leaves=[i for i in range(m) if i not in (a,c)]
  for r in range(m):
   if r==a:continue
   for bits in itertools.product((0,1),repeat=len(leaves)):
    edges=[(i,c) if bit else (c,i) for i,bit in zip(leaves,bits)]
    assert sym(pyramid(a,r,edges))==0,(a,c,r,bits)
    count+=1
simplex=tuple(tuple(int(i==j) for i in range(m)) for j in range(m))
val=sym(simplex);assert val==math.factorial(m),val
# Independent lower-dimensional controls: arbitrary segment/triangle/tetrahedron.
low=[]
for d in range(1,m-1):
 verts=tuple(tuple((j+1)**i for i in range(m)) for j in range(d+1))
 assert f(verts)==0,(d,f(verts));low.append(d)
print(json.dumps(dict(status='EXACT_VERTEX_CHECK_PASS',labelled_star_units=count,target=str(val),lower_dimension_controls=low,flags=[dict(directions=U,final_coordinate=j,weight=str(c)) for c,(U,j) in zip(coeff,flags)]),indent=2))
