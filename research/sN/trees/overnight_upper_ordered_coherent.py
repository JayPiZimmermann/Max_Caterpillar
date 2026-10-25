#!/usr/bin/env python3
"""Independent base control for an ordered coherent cubical simplex lift.

Facet maps are LINEAR maps of root lattices, not affine maps of vertex sets.
The coning orientation here is BHR's edges-wedge-head convention.
"""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import hashlib,json
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment

HERE=Path(__file__).parent


def clean(chain):return {k:v for k,v in chain.items() if v}


def delta(chain,n):
    result=defaultdict(int)
    for missing in range(n+1):
        injection=[i for i in range(n+1) if i!=missing]
        def image(vector):
            out=[0]*(n+1)
            for i,value in enumerate(vector):out[injection[i]]=value
            return tuple(out)
        for (head,edges),coefficient in chain.items():
            item=base.normalize_cube(image(head),[image(e) for e in edges],
                                     (-1)**missing*coefficient)
            if item:result[item[0]]+=item[1]
    return clean(result)


def boundary(chain):
    result=defaultdict(int)
    for (head,edges),coefficient in chain.items():
        for j,edge in enumerate(edges):
            remaining=edges[:j]+edges[j+1:]
            result[(base.addv(head,edge),remaining)]+=(-1)**j*coefficient
            result[(head,remaining)]-=(-1)**j*coefficient
    return clean(result)


def augmentation(chain):
    result=defaultdict(int)
    for (_,edges),coefficient in chain.items():result[edges]+=coefficient
    return clean(result)


def multiply(left,right):
    result=defaultdict(int)
    for (h,e),c in left.items():
        for (j,f),d in right.items():
            item=base.normalize_cube(base.addv(h,j),e+f,c*d)
            if item:result[item[0]]+=item[1]
    return clean(result)


def canonical_triangle(points):
    p,q,r=points
    v=tuple(b-a for a,b in zip(p,q));w=tuple(b-a for a,b in zip(p,r))
    if all(v[i]*w[j]==v[j]*w[i] for i,j in combinations(range(len(p)),2)):
        return None
    anchor=min(points)
    translated=[tuple(x-y for x,y in zip(point,anchor)) for point in points]
    ordered=sorted(translated)
    indices=[ordered.index(point) for point in translated]
    return tuple(ordered),base.parity(indices)


def rho_one(chain):
    result=defaultdict(int)
    for (head,edges),coefficient in chain.items():
        assert len(edges)==1
        # (head+edge) wedge head = edge wedge head.
        item=canonical_triangle(((0,)*len(head),base.addv(head,edges[0]),head))
        if item:result[item[0]]+=coefficient*item[1]
    return clean(result)


def target_boundary(n):
    assert n==4
    result=defaultdict(int)
    for missing in range(n):
        face=[i for i in range(n) if i!=missing]
        points=[base.diff(n,v,face[0]) for v in face]
        item=canonical_triangle(points)
        result[item[0]]+=(-1)**missing*item[1]
    return clean(result)


def main():
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X2={k:-v for k,v in triangle.items()}
    assert not boundary(X2)
    expected=canonical_triangle(((0,0,0),base.diff(3,1,0),base.diff(3,2,0)))
    assert rho_one(X2)=={expected[0]:expected[1]},'triangle coning sign'
    Y3=delta(X2,3)
    assert Y3,'linear root-lattice embeddings must not be replaced by affine embeddings'
    assert not boundary(Y3)
    assert not augmentation(Y3)
    assert rho_one(Y3)==target_boundary(4),'the full nonzero translated tetrahedral boundary'
    assert not delta(Y3,4),'semisimplicial delta squared'
    edge={((0,)*4,(base.diff(4,1,0),)):1}
    tail=attachment.raw_chain(4,(((1,2,3),1,1),))
    X3=multiply(edge,tail)
    assert boundary(X3)==Y3,'explicit coherent tetrahedral filling'
    Y4=delta(X3,4)
    left=attachment.raw_chain(5,(((0,1,2),2,-1),))
    right=attachment.raw_chain(5,(((2,3,4),2,1),))
    product=multiply(left,right)
    assert Y4=={k:-v for k,v in product.items()},'two-triangle-cycle factorization'
    assert not boundary(Y4)
    records=[]
    for (head,edges),coefficient in sorted(Y3.items()):
        records.append(dict(head=head,edges=edges,coefficient=int(coefficient)))
    result=dict(status='EXACT_NONZERO_ORDERED_TETRAHEDRAL_BASE_CONTROL',
                triangle_cube_count=len(X2),tetrahedral_cube_count=len(Y3),
                tetrahedral_cubes=records,target_triangle_count=len(rho_one(Y3)),
                boundary_zero=True,augmentation_zero=True,delta_squared_zero=True,
                explicit_X3_cube_count=len(X3),ordered_Y4_cube_count=len(Y4),
                ordered_Y4_factorization='-Gamma_{012;root2,reflection-} * Gamma_{234;root2,reflection+}',
                coning_orientation='BHR edges-wedge-head; X2 is minus the oriented triangle boundary.',
                facet_maps='Linear root-lattice maps e_j-e_i -> e_mu(j)-e_mu(i); every face resets its own first vertex to zero.',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Exact base check for a coherent ordered recurrence. Does not bound the support growth of repeated fillings.')
    (HERE/'overnight_upper_ordered_coherent.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
