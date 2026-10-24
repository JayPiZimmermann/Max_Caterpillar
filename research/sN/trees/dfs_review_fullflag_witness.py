#!/usr/bin/env python3
"""Check proposed nonpath Fourier identity with complete subspace-flag arrays.
All arithmetic is exact. Vanishing arrays are a complete-flag identity;
identifying their kernel with L_(m-2) requires the reconstruction theorem.
"""
import sys,json,itertools,time
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'all_tree_dfs'))
from complete_flags import pyramid,simplex,sub
m=int(sys.argv[1]) if len(sys.argv)>1 else 6
D=json.loads((HERE/f'dfs_review_fourier_witness_{m}_nopath.json').read_text());start=time.time()
e=[tuple(int(i==j) for i in range(m)) for j in range(m)]
out=defaultdict(Fraction)
for i,(c,u) in enumerate(zip(D['coefficients'],D['representatives'])):
 c=Fraction(c)
 if not c:continue
 h=sub(e[u['root']],e[0]);gs=[sub(e[a],e[b]) for a,b in u['edges']]
 for p in itertools.permutations(range(m)):
  hh=tuple(h[t] for t in p);gg=tuple(sorted(tuple(g[t] for t in p) for g in gs))
  for key,v in pyramid(hh,gg).items():out[key]+=c*Fraction(v)
 out={k:v for k,v in out.items() if v};out=defaultdict(Fraction,out)
 print('orbit',i,'nonzero flags',len(out),'elapsed',round(time.time()-start,2),flush=True)
target=simplex(tuple(e))
nonzero={k:out.get(k,0)-target.get(k,0) for k in set(out)|set(target) if out.get(k,0)!=target.get(k,0)}
negative={k:out.get(k,0)+target.get(k,0) for k in set(out)|set(target) if out.get(k,0)!=-target.get(k,0)}
status='ALL_COMPLETE_FLAGS_EQUAL' if not nonzero else ('ALL_COMPLETE_FLAGS_NEGATIVE_TARGET' if not negative else 'COMPLETE_FLAG_COUNTEREXAMPLE')
result=dict(m=m,status=status,nonzero_entries=len(nonzero),negative_target_discrepancies=len(negative),elapsed=time.time()-start)
if nonzero:result['first_counterexample']=str(next(iter(nonzero.items())))
print(json.dumps(result,indent=2),flush=True)
(HERE/f'dfs_review_fullflag_witness_{m}.json').write_text(json.dumps(result,indent=2)+'\n')
