#!/usr/bin/env python3
"""Use the explicit product-homotopy seed before noncrossing corrections."""
from pathlib import Path
import hashlib,json,time
import overnight_upper_ordered_noncrossing as nc
import overnight_upper_ordered_product_homotopy as homotopy
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_coherent as coherent

HERE=Path(__file__).parent


def main():
    start=time.monotonic()
    descriptors=(((0,1,2),2,-1),((2,3,4),2,1))
    X=homotopy.product_homotopy(5,descriptors)
    scalar=2;records=[]
    for dimension in (4,5):
        _,Y,record=nc.correct(X,dimension+1)
        record['from_simplex_dimension']=dimension
        if Y is None:
            records.append(record);break
        scalar*=record['scale']
        X,stats=contraction.contract(Y,dimension+2)
        assert coherent.boundary(X)==Y
        record.update(target_scalar=scalar,to_simplex_dimension=dimension+1,
                      filling=stats,output_cubes=len(X))
        records.append(record)
        print('P SEEDED NC',dimension,record['ranks'],'CUBES',len(X),
              'SECONDS',time.monotonic()-start,flush=True)
    result=dict(status='EXACT_PRODUCT_SEEDED_NONCROSSING_PRIMITIVE_CONTROLS',records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start,
                scope='Tests this explicit P-homotopy seed followed by the stated star contraction and NC augmentation correction. A failure is not a no-go theorem for all choices of coherent lift.')
    (HERE/'overnight_upper_ordered_noncrossing_seed.json').write_text(json.dumps(result,indent=2)+'\n')
    print('P SEEDED NC COMPLETE',[(r['from_simplex_dimension'],r['ranks']) for r in records],flush=True)


if __name__=='__main__':main()
