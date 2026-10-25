#!/usr/bin/env python3
"""Check H S on actual ordered lifts, not arbitrary Koszul monomials."""
from collections import defaultdict,Counter
from pathlib import Path
import hashlib,json,time
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction

HERE=Path(__file__).parent


def main():
    start=time.monotonic()
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X,_=contraction.contract(coherent.delta({k:-v for k,v in triangle.items()},3),4)
    records=[]
    for dimension in (3,4,5):
        labels=dimension+1
        HX,_=contraction.contract(X,labels)
        assert not HX,'H squared is zero on the actual lift'
        doubled=contraction.double(X)
        HSX,stats=contraction.contract(doubled,labels)
        expanded=contraction.expand_basis(contraction.to_abstract(X,labels),labels,True)
        star_min=Counter(min(i for kind,i,_ in edges if kind==0) for _,edges in expanded)
        record=dict(simplex_dimension=dimension,lift_cubes=len(X),doubled_cubes=len(doubled),
                    H_S_cubes=len(HSX),H_S_zero=not HSX,star_min_histogram=dict(star_min),
                    contraction=stats)
        if HSX:
            record['first_nonzero_H_S_cube']=str(next(iter(HSX.items())))
        records.append(record)
        print('ACTUAL H S',record,'SECONDS',time.monotonic()-start,flush=True)
        if dimension==5:break
        degree=dimension-1
        Y=coherent.delta(X,labels)
        corrected=defaultdict(int,{key:2**degree*value for key,value in Y.items()})
        for key,value in contraction.double(Y).items():corrected[key]-=value
        X,_=contraction.contract(coherent.clean(corrected),labels+1)
    result=dict(status='EXACT_DOUBLING_CONTRACTION_ON_ORDERED_STATES',records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start,
                scope='Tests the concrete star-Koszul contraction on actual integer-scaled ordered simplex lifts. A nonzero H S X rules out simply discarding root-preserving facets at chain level.')
    (HERE/'overnight_upper_ordered_doubling.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
