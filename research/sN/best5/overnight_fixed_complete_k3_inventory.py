"""Exact combinatorial size of the complete-comparison K3 locality domain.

No LP, coefficient filter, or producer flat pickle is used. The previously
proved15-circuit means every zero subset of size<=13 is a nonzero flat.
"""
from itertools import combinations
from pathlib import Path
import time,json,hashlib
import numpy as np


def main():
    start=time.monotonic();rel=[frozenset(s)for n in(3,4)for s in combinations(range(5),n)];idx={s:i for i,s in enumerate(rel)};req=[(1<<idx[T])|(1<<idx[T|{o}])for T in rel if len(T)==3 for o in range(5)if o not in T];n=1<<20;hist=np.zeros(n,dtype=np.int64);flats=0
    for z in range(1<<15):
        if z.bit_count()>13:continue
        cov=sum(1<<i for i,r in enumerate(req)if z&r==r);hist[cov]+=1;flats+=1
    sub=hist.copy()
    for j in range(20):
        blocks=sub.reshape(-1,2,1<<j);blocks[:,1,:]+=blocks[:,0,:]
    assert int(sub[-1])==flats
    counts={}
    for k in(1,2,3):
        out=sub**k
        for j in range(20):
            blocks=out.reshape(-1,2,1<<j);blocks[:,1,:]-=blocks[:,0,:]
        assert np.all(out>=0);counts[k]=int(out[-1])
    unordered=(counts[3]+3*counts[2]+2*counts[1])//6;assert( counts[3]+3*counts[2]+2*counts[1])%6==0
    report={'status':'EXACT_COMBINATORIAL_INVENTORY_ONLY','nonzero_flats':flats,'distinct_coverage_masks':int(np.count_nonzero(hist)),'ordered_covers':counts,'unordered_covering_triples':unordered,'lower_bound_S5_orbits':(unordered+119)//120,'upper_bound_S5_orbits':unordered,'signed_cases_before_label_symmetry':8*unordered,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'All nonzero closed vanishing flats, arbitrary real coefficients. Count uses the independently proved15-circuit. No infeasibility or construction claim.'};Path('overnight_fixed_complete_k3_inventory.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True))
if __name__=='__main__':main()
