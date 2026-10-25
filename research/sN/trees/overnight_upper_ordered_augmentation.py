#!/usr/bin/env python3
"""Can a closed correction remove the next ordered augmentation obstruction?"""
from collections import defaultdict
from itertools import combinations,product
from pathlib import Path
import hashlib,json
from flint import fmpq_mat
import overnight_upper_ordered_product_homotopy as homotopy
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_coherent as coherent

HERE=Path(__file__).parent


def cycle_basis(n):return tuple((i,j) for i in range(1,n) for j in range(1,i))


def delta_wedge(n,wedge):
    result=defaultdict(int)
    for missing in range(n+1):
        injection=[i for i in range(n+1) if i!=missing]
        factors=[]
        for i,j in wedge:
            a,b,c=injection[i],injection[j],injection[0]
            factor=[((a,b),1)]
            if c:
                factor += [((a,c),-1),((b,c),1)]
            factors.append(factor)
        for choice in product(*factors):
            edges=[e for e,_ in choice]
            if len(set(edges))<len(edges):continue
            sign=(-1)**(missing+sum(edges[i]>edges[j] for i in range(len(edges)) for j in range(i+1,len(edges))))
            for _,coefficient in choice:sign*=coefficient
            result[tuple(sorted(edges))]+=sign
    return coherent.clean(result)


def homology_projection(chain,n):
    result=defaultdict(int)
    expanded=contraction.expand_basis(contraction.to_abstract(chain,n),n,True)
    for (_,edges),coefficient in expanded.items():
        if all(kind==1 for kind,_,_ in edges):
            result[tuple((i,j) for _,i,j in edges)]+=coefficient
    return coherent.clean(result)


def main():
    descriptors=(((0,1,2),2,-1),((2,3,4),2,1))
    X=homotopy.product_homotopy(5,descriptors)
    Y=coherent.delta(X,5)
    target=homology_projection(Y,6)
    source=list(combinations(cycle_basis(5),3))
    destination=list(combinations(cycle_basis(6),3))
    columns=[delta_wedge(5,c) for c in source]
    rows=[[c.get(edge,0) for c in columns]+[target.get(edge,0)] for edge in destination]
    ordinary=fmpq_mat([r[:-1] for r in rows]).rank()
    augmented=fmpq_mat(rows).rank()
    result=dict(status='EXACT_ORDERED_AUGMENTATION_CORRECTION_TEST',
                source_labels=5,target_labels=6,degree=3,
                source_basis=source,target_basis=destination,integer_rows=rows,
                ranks=[ordinary,augmented],target_nonzero_wedges=len(target),
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='All closed degree3 cubical corrections to the ordered X4 lift are covered through their exterior cycle-space augmentations. A rank gap means no such correction can eliminate the next augmentation obstruction.')
    if ordinary==augmented:
        rr,rank=fmpq_mat(rows).rref();coefficients=['0']*len(source)
        for i in range(rank):
            pivot=next(j for j in range(len(source)) if rr[i,j])
            coefficients[pivot]=str(rr[i,len(source)])
        result['correction_coefficients']=coefficients
    else:
        # The rightmost pivot in the augmented matrix is an exact witness;
        # store the full tiny integer system for independent rational replay.
        result['verdict']='NO_CLOSED_CORRECTION_CAN_REMOVE_THIS_AUGMENTATION'
    (HERE/'overnight_upper_ordered_augmentation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],result['ranks'],result.get('verdict',result.get('correction_coefficients')),flush=True)


if __name__=='__main__':main()
