"""Independent exact completeness check for every P4 flat arrangement.

Does not recompute the producer's nullspace algorithm. Each supplied ray
must be the intersection of rank d-1 normals. Its annihilated-normal set
covers subsets of size d-1; all such subsets must be covered. In particular
every independent d-1 tuple has its unique kernel ray in the inventory.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,math,time
import overnight_root9_equations as E


def main():
    start=time.monotonic();E.initialize();here=Path(__file__).parent;path=here/'overnight_fixed_p4_flat_rays.jsonl';records={}
    for line in path.read_text().splitlines():
        rec=json.loads(line);assert rec['flat']not in records;records[rec['flat']]=rec
    assert set(records)==set(E.arithmetic.BASES);total_rays=total_subsets=0
    for z in sorted(records):
        rec=records[z];forms=E.arithmetic.flat(z)[0];d=len(E.arithmetic.BASES[z]);m=len(forms);assert(rec['dimension'],rec['forms'])==(d,m);assert len(E.arithmetic.rref(forms))==d;seen=set();covered=set()
        for raw in rec['rays']:
            r=tuple(raw);assert len(r)==d and any(r)and math.gcd(*r)==1 and next(v for v in r if v)>0 and r not in seen;seen.add(r)
            zeros=[j for j,f in enumerate(forms)if sum(a*b for a,b in zip(f,r))==0];assert len(E.arithmetic.rref([forms[j]for j in zeros]))==d-1
            for subset in combinations(zeros,d-1):covered.add(subset)
        assert len(covered)==math.comb(m,d-1),(z,len(covered),math.comb(m,d-1));total_subsets+=len(covered);total_rays+=len(seen)
    report={'status':'INDEPENDENT_EXACT_ALL_FLAT_RAY_COVER_PASS','flats':len(records),'rays':total_rays,'covered_normal_subsets':total_subsets,'seconds':time.monotonic()-start,'data_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Complete real-parameter absolute-form fans for the fixed P4 flat atlas. Convexification only; it does not itself exclude a network.'};(here/'overnight_fixed_p4_flat_rays_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
