#!/usr/bin/env python3
"""Three-square triangle homotopy and its ordered nonproduct filling."""
from collections import defaultdict
from pathlib import Path
import hashlib,json,time
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction

HERE=Path(__file__).parent


def linear_sum(*terms):
    out=defaultdict(int)
    for coefficient,chain in terms:
        for key,value in chain.items():out[key]+=coefficient*value
    return coherent.clean(out)


def triangle_homotopy(n,descriptor):
    triangle,root,sign=descriptor
    first,second=[v for v in triangle if v!=root]
    u=tuple(sign*x for x in base.diff(n,first,root))
    v=tuple(sign*x for x in base.diff(n,second,root))
    b=tuple(y-x for x,y in zip(u,v))
    out=defaultdict(int)
    for head,edges,coefficient in ((u,(u,b),1),((0,)*n,(u,v),-1),(u,(b,v),-1)):
        item=base.normalize_cube(head,edges,coefficient)
        if item:out[item[0]]+=item[1]
    return coherent.clean(out)


def product_homotopy(n,descriptors):
    factors=[attachment.raw_chain(n,(d,)) for d in descriptors]
    primitives=[triangle_homotopy(n,d) for d in descriptors]
    doubled=[contraction.double(f) for f in factors]
    total=defaultdict(int)
    unit={((0,)*n,()):1}
    for i in range(len(factors)):
        term=unit
        for f in factors[:i]:term=coherent.multiply(term,f)
        term=coherent.multiply(term,primitives[i])
        for f in doubled[i+1:]:term=coherent.multiply(term,f)
        for key,value in term.items():total[key]+=(-1)**i*2**i*value
    return coherent.clean(total)


def serialize(chain):
    return [[list(head),[list(e) for e in edges],int(c)] for (head,edges),c in sorted(chain.items())]


def main():
    start=time.monotonic();checks=0
    for n in (3,4,5):
        for root in (0,1,n-1):
            for sign in (-1,1):
                descriptor=((0,1,n-1),root,sign)
                gamma=attachment.raw_chain(n,(descriptor,))
                P=triangle_homotopy(n,descriptor)
                assert coherent.boundary(P)==linear_sum((1,contraction.double(gamma)),(-2,gamma))
                checks+=1
    descriptors=(((0,1,2),2,-1),((2,3,4),2,1))
    Y4={k:-v for k,v in attachment.raw_chain(5,descriptors).items()}
    X4=product_homotopy(5,descriptors)
    assert coherent.boundary(X4)==linear_sum((4,Y4),(-1,contraction.double(Y4)))
    Y5=coherent.delta(X4,5)
    assert not coherent.boundary(Y5)
    corrected=linear_sum((8,Y5),(-1,contraction.double(Y5)))
    X5,stats=contraction.contract(corrected,6)
    assert coherent.boundary(X5)==corrected
    result=dict(status='EXACT_TRIANGLE_PRODUCT_HOMOTOPY_AND_ORDERED_EXTENSION',
                local_homotopy_controls=checks,local_squares=3,
                product_primitive_bound='3^k(2^k-1) < 6^k cubes before cancellations',
                X4_cube_count=len(X4),X4_target_scalar=2,X4_cubes=serialize(X4),
                Y5_cube_count=len(Y5),Y5_cubes=serialize(Y5),
                next_corrected_boundary_cubes=len(corrected),X5_cube_count=len(X5),
                X5_target_scalar=12,next_contraction=stats,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start,
                scope='The explicit local and product homotopies are uniform. The ordered X4/X5 calculations are exact finite chain controls; no global closure or exponential width is proved.')
    (HERE/'overnight_upper_ordered_product_homotopy.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PRODUCT HOMOTOPY',len(X4),'X4 CUBES',len(Y5),'Y5 CUBES',len(X5),'X5 CUBES',
          'SECONDS',result['seconds'],flush=True)


if __name__=='__main__':main()
