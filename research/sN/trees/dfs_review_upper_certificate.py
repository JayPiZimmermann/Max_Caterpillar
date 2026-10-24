#!/usr/bin/env python3
"""Recheck the saved N=5 upper certificate using only its nonzero support.
No LP and no full-dictionary matrix are constructed. Rebuild every exact
chamber/crossing equation directly from the supplied coefficient records.
"""
import sys,json,itertools,time,math
from fractions import Fraction as F
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'construct'))
from nonsym import exact_rows
start=time.time();src=HERE/'all_tree_dfs/cyclic_upper_5_desc1.json';D=json.loads(src.read_text())
n=D['n'];records=D['coefficients']
neurons=[(r['head'],{tuple(e):1 for e in r['M']}) for r in records]
coefs=[F(r['coefficient']) for r in records];aux=[F(x) for x in D['aux']]
assert all(coefs) and all(sum(h)==0 for h,W in neurons)
assert len(aux)==n+n*(n-1)//2
eqs,nv=exact_rows(n,neurons);x=coefs+aux
assert len(x)==nv
bad=[i for i,(row,b) in enumerate(eqs) if sum(c*x[j] for j,c in row.items())!=b]
# Independent pointwise convention control: W_(i,j) means sigma(x_i-x_j),
# while the auxiliary pair columns are max(x_i,x_j).
pairs=list(itertools.combinations(range(n),2));point_failures=[]
for pt in itertools.product((-2,-1,0,1,2),repeat=n):
 val=sum(c*max(0,sum(a*t for a,t in zip(h,pt))+sum(max(0,pt[i]-pt[j]) for i,j in W)) for c,(h,W) in zip(coefs,neurons))
 val+=sum(b*t for b,t in zip(aux[:n],pt))
 val+=sum(c*max(pt[i],pt[j]) for c,(i,j) in zip(aux[n:],pairs))
 if val!=max(pt):point_failures.append(pt)
result=dict(status='EXACT_SUPPORT_RECHECK_PASS' if not bad and not point_failures else 'FAIL',
 n=n,units=len(records),auxiliary_channels=2,second_width=len(records)+2,
 chamber_count=math.factorial(n),
 exact_equations=len(eqs),equation_failures=bad,grid_points=5**n,point_failures=point_failures,
 aux_nonzero=sum(bool(a) for a in aux),elapsed=time.time()-start)
print(json.dumps(result,indent=2),flush=True)
(HERE/'dfs_review_upper_certificate_5.json').write_text(json.dumps(result,indent=2)+'\n')
