#!/usr/bin/env python3
"""Exact ordered lifts using closed augmentation corrections instead of doubling."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,math,time
from flint import fmpq_mat
import overnight_upper_triangle_attachments as attachment
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_augmentation as augmentation

HERE=Path(__file__).parent


def correction(X,labels):
    degree=labels-2
    Y=coherent.delta(X,labels)
    target=augmentation.homology_projection(Y,labels+1)
    source=list(combinations(augmentation.cycle_basis(labels),degree))
    destination=list(combinations(augmentation.cycle_basis(labels+1),degree))
    columns=[augmentation.delta_wedge(labels,c) for c in source]
    rows=[[c.get(edge,0) for c in columns]+[target.get(edge,0)] for edge in destination]
    rr,rank=fmpq_mat(rows).rref()
    pivots=[next(j for j in range(len(source)+1) if rr[i,j]) for i in range(rank)]
    assert len(source) not in pivots,'augmentation correction exact consistency'
    coefficients=[Q(0)]*len(source)
    for i,pivot in enumerate(pivots):coefficients[pivot]=Q(str(rr[i,len(source)]))
    scale=math.lcm(*(c.denominator for c in coefficients))
    abstract={((0,)*(labels-1),tuple((1,i,j) for i,j in edges)):int(c*scale)
              for c,edges in zip(coefficients,source) if c}
    closed=contraction.from_abstract(contraction.expand_basis(abstract,labels,False),labels)
    assert not coherent.boundary(closed)
    fixed=defaultdict(int,{key:scale*value for key,value in X.items()})
    for key,value in closed.items():fixed[key]-=value
    fixed=coherent.clean(fixed)
    next_boundary=coherent.delta(fixed,labels)
    assert not coherent.boundary(next_boundary)
    assert not coherent.augmentation(next_boundary),'complete augmentation cancellation'
    return fixed,next_boundary,dict(source_columns=len(source),target_rows=len(destination),
                                   rank=rank,correction_wedges=len(abstract),scale=scale,
                                   closed_correction_cubes=len(closed),corrected_lift_cubes=len(fixed),
                                   next_boundary_cubes=len(next_boundary))


def main():
    start=time.monotonic()
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X,_=contraction.contract(coherent.delta({k:-v for k,v in triangle.items()},3),4)
    scalar=1;records=[]
    dest=HERE/'overnight_upper_ordered_undoubled.json'
    result=dict(status='BOUNDED_EXACT_ORDERED_LIFTS_WITHOUT_DOUBLING',records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Each completed correction and filling is checked as a formal cubical identity. This is not yet a uniform quantitative construction.')
    for dimension in (3,4,5):
        labels=dimension+1
        if len(X)>30000:
            records.append(dict(simplex_dimension=dimension,status='PREDECLARED_SUPPORT_STOP',cubes=len(X)))
            break
        fixed,Y,stats=correction(X,labels)
        scalar*=stats['scale']
        X,fill=contraction.contract(Y,labels+1)
        assert coherent.boundary(X)==Y
        record=dict(from_simplex_dimension=dimension,to_simplex_dimension=dimension+1,
                    target_scalar=scalar,correction=stats,filling=fill,
                    output_cubes=len(X),max_head_l1=max(sum(abs(v) for v in h[1:]) for h,_ in X))
        records.append(record)
        result['seconds']=time.monotonic()-start
        dest.write_text(json.dumps(result,indent=2)+'\n')
        print('UNDOUBLED ORDERED',record,'SECONDS',result['seconds'],flush=True)
    result['seconds']=time.monotonic()-start
    dest.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
