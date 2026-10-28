"""Find a small exact evaluation contradiction for the corrected selector pattern.

This is a linear-algebra producer only. A separate standard-library checker
will regenerate every original equation from points and feature functions.
"""
import hashlib,itertools,json,time
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_fullpair_pattern import EDGES
from overnight_fixed_selector_flatten import values


def main():
 start=time.monotonic();basis={};records=[];witness=None
 def add(row,rhs,label):
  nonlocal witness
  index=len(records);records.append({'label':label,'row':row,'rhs':rhs});v=list(map(Q,row))+[Q(rhs)];comb={index:Q(1)}
  for pivot,(b,co)in sorted(basis.items()):
   t=v[pivot]
   if t:
    v=[x-t*y for x,y in zip(v,b)]
    for j,c in co.items():comb[j]=comb.get(j,Q(0))-t*c
  pivot=next((j for j,c in enumerate(v[:-1])if c),None)
  if pivot is None:
   if v[-1]:witness={'terms':[{'record':j,'coefficient':str(c/v[-1])}for j,c in comb.items()if c],'rhs':'1'}
   return
  p=v[pivot];basis[pivot]=([c/p for c in v],{j:c/p for j,c in comb.items()if c})
 points=[(0,)+v for v in itertools.product((-2,-1,0,1,2),repeat=4)if any(v)];points.sort(key=lambda x:(max(map(abs,x)),sum(map(abs,x)),x))
 for x in points:
  phi=[max(x[i]-x[j],0)for i,j in EDGES];g=values(x);add(phi+[c*int(g[0]>0)for c in phi]+[c*int(g[1]>0)for c in phi]+[-c*int(g[2]>0)for c in phi],max(x),{'kind':'value','point':x})
  if witness:break
  for j,c in enumerate(g):
   if not c:
    row=[0]*56;row[14*(j+1):14*(j+2)]=phi;add(row,0,{'kind':'zero','point':x,'unit':j})
    if witness:break
  if witness:break
 result={'status':'EXACT_LINEAR_EVALUATION_CONTRADICTION'if witness else'NO_LINEAR_CONTRADICTION_ON_GRID','records':records,'witness':witness,'rank':len(basis),'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_selector_pair_obstruction.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('records','witness')}));print('witness_terms',len(witness['terms'])if witness else None)

if __name__=='__main__':main()
