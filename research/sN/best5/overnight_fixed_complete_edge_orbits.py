"""Complete closed cover of four-tie-zero K3 systems by edge-zero colors."""
from pathlib import Path
from itertools import combinations,permutations,product
import numpy as np,json,time,hashlib


def main():
    start=time.monotonic();edges=list(combinations(range(5),2));codes=np.arange(3**10,dtype=np.int64);powers=3**np.arange(10,dtype=np.int64);digits=(codes[:,None]//powers[None,:])%3;canon=np.empty(len(codes),dtype=np.int64)
    for code,row in enumerate(digits):
        seen={};out=[]
        for color in row:
            c=int(color)
            if c not in seen:seen[c]=len(seen)
            out.append(seen[c])
        canon[code]=sum(c*int(p)for c,p in zip(out,powers))
    keys=canon.copy()
    for perm in permutations(range(5)):
        moved=[edges.index(tuple(sorted((perm[i],perm[j]))))for i,j in edges];newcodes=np.sum(digits[:,np.argsort(moved)]*powers[None,:],axis=1);keys=np.minimum(keys,canon[newcodes])
    reps,counts=np.unique(keys,return_counts=True);rows=[{'code':int(c),'colors':[int(v)for v in digits[c]],'orbit_size':int(n)}for c,n in zip(reps,counts)];out={'status':'EXACT_EDGE_COLOR_COVER_PRODUCED','edge_order':edges,'assignments':3**10,'orbits':rows,'orbit_count':len(rows),'sum_orbit_sizes':sum(r['orbit_size']for r in rows),'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Every edge is assigned to one zero core coefficient. Additional zero coefficients are allowed; this covers all four-tie-zero K3 representations. Output signs must be checked for all choices of distinguished minority color.'};Path('overnight_fixed_complete_edge_orbits.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='orbits'},sort_keys=True))
if __name__=='__main__':main()
