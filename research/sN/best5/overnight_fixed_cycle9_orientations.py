"""Exact feature-factorization gate for C5 comparisons and anchors0,2."""
from fractions import Fraction as Q
from itertools import permutations,product
from pathlib import Path
import json,time,hashlib
from overnight_fixed_bowtie_verify import rref
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();base=[(0,1),(1,2),(2,3),(3,4),(4,0)];lin=[Q(i==2)-Q(i==0)for i in range(5)];results=[]
    for signs in product((1,-1),repeat=5):
        edges=[(i,j)if s>0 else(j,i)for(i,j),s in zip(base,signs)];A=[[Q(t==i)-Q(t==j)for t in range(5)]for i,j in edges];cells={}
        for p in permutations(range(5)):
            rank={v:i for i,v in enumerate(p)};act=[row if rank[i]<rank[j]else[Q(0)]*5 for row,(i,j)in zip(A,edges)];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'maxima':set(),'example':p});cell['maxima'].add(p[0])
        assert len(cells)==30 and all(len(c['maxima'])<=2 for c in cells.values());witness=None
        for key,c in cells.items():
            B=c['active']+[lin];rank=len(rref(B))
            for top in sorted(c['maxima']):
                target=[Q(i==top)-Q(i==0)for i in range(5)]
                if len(rref(B+[target]))>rank:witness={'cell':key,'possible_maximum':top,'active_rows':[[str(v)for v in row]for row in B]};break
            if witness:break
        results.append({'orientation':signs,'edges':edges,'status':'CELL_FACTORISATION_PASS'if witness is None else'EXACT_FEATURE_FACTORISATION_FAILURE','witness':witness})
    survivors=[r for r in results if r['witness']is None];out={'status':'COMPLETE32_CYCLE_ORIENTATION_GATE','surviving_orientations':len(survivors),'results':results,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Failure certifies no factorization through the five invariant comparison functions plus x2−x0. Positive common-translation tails make this necessary for any second width with the four physical anchor rows. Passing is only necessary, not a ReLU construction.'};(HERE/'overnight_fixed_cycle9_orientations.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print('SURVIVORS',[(r['orientation'],r['edges'])for r in survivors],flush=True);print('SECONDS',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
