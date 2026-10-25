#!/usr/bin/env python3
"""Standalone integer check of the nine-square coherent ordered facet lift."""
from collections import defaultdict
from itertools import permutations
from pathlib import Path
import hashlib,json

HERE=Path(__file__).parent


def plus(x,y):return tuple(a+b for a,b in zip(x,y))
def minus(x,y):return tuple(a-b for a,b in zip(x,y))
def det3(cols):
    return sum((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))*
               cols[0][p[0]]*cols[1][p[1]]*cols[2][p[2]] for p in permutations(range(3)))


def triangle(vertices):
    out=[]
    for i,j,c in ((0,1,1),(1,2,1),(0,2,-1)):
        h=vertices[i];v=minus(vertices[j],h)
        if v.index(1)<v.index(-1):h=vertices[j];v=tuple(-x for x in v);c=-c
        out.append((h,v,c))
    return out


def boundary(chain):
    out=defaultdict(int)
    for (h,(a,b)),c in chain.items():
        for p,v,s in ((plus(h,a),b,1),(h,b,-1),(plus(h,b),a,-1),(h,a,1)):out[(p,v)]+=c*s
    return {k:v for k,v in out.items() if v}


def main():
    e=[tuple(int(i==j) for i in range(5)) for j in range(5)]
    A=triangle(e[:3]);B=triangle([tuple(-x for x in e[i]) for i in (2,3,4)])
    chain=defaultdict(int)
    for h,a,c in A:
        for k,b,d in B:
            edges=(a,b);coefficient=c*d
            if a>b:edges=(b,a);coefficient=-coefficient
            chain[(plus(h,k),edges)]+=coefficient
    assert len(chain)==9 and not boundary(chain)
    facets={};corner=[]
    for (h,(a,b)),c in chain.items():
        supports=[{i for i,x in enumerate(v) if x} for v in (a,b)]
        if supports[0]&supports[1]:
            assert h==tuple(-x-y for x,y in zip(a,b))
            corner.append(dict(head=h,edges=[a,b],coefficient=c));continue
        missing=next(i for i in range(5) if i not in supports[0]|supports[1])
        facet=tuple(i for i in range(5) if i!=missing)
        orientation=det3([[v[i] for i in facet[1:]] for v in (h,a,b)])
        assert c==(-1)**missing*(-orientation)
        assert missing not in facets;facets[missing]=dict(head=h,edges=[a,b],coefficient=c,orientation=orientation)
    assert len(facets)==5 and len(corner)==4
    for h,edges in chain:
        (i,j),(k,l)=[sorted(v for v,x in enumerate(edge) if x) for edge in edges]
        assert not (i<k<j<l or k<i<l<j)
    augmentation=defaultdict(int)
    for (h,edges),c in chain.items():augmentation[edges]+=c
    augmentation={k:v for k,v in augmentation.items() if v}
    out=dict(status='EXACT_NINE_SQUARE_ORDERED_FACET_CYCLE',triangle_A=[0,1,2],negative_triangle_B=[2,3,4],
             chain=[dict(head=h,edges=es,coefficient=c) for (h,es),c in sorted(chain.items())],
             tetrahedron_facets=facets,corner_corrections=corner,boundary_zero=True,all_base_edges_noncrossing=True,
             augmentation=[dict(edges=es,coefficient=c) for es,c in sorted(augmentation.items())],augmentation_zero=not augmentation,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='A coherent cubical representative of the boundary of the four-simplex. This is not a nine-unit max5 network or a uniform exponential construction.')
    (HERE/'overnight_upper_ordered_product.json').write_text(json.dumps(out,indent=2)+'\n')
    print(out['status'],'5 FACET SQUARES +4 CORNER CORRECTIONS; AUGMENTATION NONZERO')


if __name__=='__main__':main()
