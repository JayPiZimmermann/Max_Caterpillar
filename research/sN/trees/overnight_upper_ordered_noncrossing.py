#!/usr/bin/env python3
"""Exact fixed-order noncrossing corrections in the undoubled recurrence."""
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
import overnight_upper_ordered_product_homotopy as homotopy

HERE=Path(__file__).parent


def crosses(e,f):
    a,b=sorted(e);c,d=sorted(f)
    return a<c<b<d or c<a<d<b


def correct(X,labels):
    degree=labels-2
    Y=coherent.delta(X,labels)
    target=augmentation.homology_projection(Y,labels+1)
    source=[g for g in combinations(augmentation.cycle_basis(labels),degree)
            if not any(crosses(e,f) for e,f in combinations(g,2))]
    destination=list(combinations(augmentation.cycle_basis(labels+1),degree))
    columns=[augmentation.delta_wedge(labels,g) for g in source]
    rows=[[c.get(edge,0) for c in columns]+[target.get(edge,0)] for edge in destination]
    rr,rank=fmpq_mat(rows).rref()
    pivots=[next(j for j in range(len(source)+1) if rr[i,j]) for i in range(rank)]
    gap=len(source) in pivots
    record=dict(source_graphs=source,source_columns=len(source),target_rows=len(destination),
                ranks=[rank-int(gap),rank],target_nonzero_wedges=len(target))
    if gap:
        record.update(status='EXACT_NONCROSSING_CORRECTION_FAILURE',integer_rows=rows)
        return None,None,record
    coefficients=[Q(0)]*len(source)
    for i,pivot in enumerate(pivots):coefficients[pivot]=Q(str(rr[i,len(source)]))
    scale=math.lcm(*(c.denominator for c in coefficients))
    abstract={((0,)*(labels-1),tuple((1,i,j) for i,j in edges)):int(c*scale)
              for c,edges in zip(coefficients,source) if c}
    closed=contraction.from_abstract(contraction.expand_basis(abstract,labels,False),labels)
    assert not coherent.boundary(closed)
    fixed=defaultdict(int,{key:scale*value for key,value in X.items()})
    for key,value in closed.items():fixed[key]-=value
    fixed=coherent.clean(fixed);boundary=coherent.delta(fixed,labels)
    assert not coherent.boundary(boundary) and not coherent.augmentation(boundary)
    record.update(status='EXACT_NONCROSSING_AUGMENTATION_CORRECTION',
                  coefficients=list(map(str,coefficients)),scale=scale,
                  correction_wedges=len(abstract),closed_correction_cubes=len(closed),
                  corrected_lift_cubes=len(fixed),next_boundary_cubes=len(boundary))
    return fixed,boundary,record


def main():
    start=time.monotonic();records=[]
    descriptors=(((0,1,2),2,-1),((2,3,4),2,1))
    _,_,control=correct(homotopy.product_homotopy(5,descriptors),5)
    assert control['ranks']==[16,16]
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X,_=contraction.contract(coherent.delta({k:-v for k,v in triangle.items()},3),4)
    scalar=1
    result=dict(status='BOUNDED_ORDERED_NONCROSSING_PRIMITIVE_TEST',records=records,
                product_homotopy_X4_control=control,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Only the augmentation primitive is restricted to fixed-order noncrossing graphs. Actual corrected chains and fillings are checked. No all-N closure or support bound is presumed.')
    dest=HERE/'overnight_upper_ordered_noncrossing.json'
    for dimension in (3,4,5):
        fixed,Y,record=correct(X,dimension+1)
        record['from_simplex_dimension']=dimension
        if fixed is None:
            records.append(record);break
        scalar*=record['scale']
        X,stats=contraction.contract(Y,dimension+2)
        assert coherent.boundary(X)==Y
        record.update(to_simplex_dimension=dimension+1,target_scalar=scalar,
                      filling=stats,output_cubes=len(X))
        records.append(record)
        result['seconds']=time.monotonic()-start
        dest.write_text(json.dumps(result,indent=2)+'\n')
        print('ORDERED NC',dimension,record['ranks'],record['correction_wedges'],
              'NEXT CUBES',len(X),'SECONDS',result['seconds'],flush=True)
    result['seconds']=time.monotonic()-start
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print('ORDERED NC COMPLETE',[(r['from_simplex_dimension'],r['ranks']) for r in records],flush=True)


if __name__=='__main__':main()
