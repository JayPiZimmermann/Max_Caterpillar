#!/usr/bin/env python3
"""Smallest span-plane control for a uniform ghost-root triangle product."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import hashlib,json,math,sys,time
import sympy as sp

HERE=Path(__file__).parent


def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))


def triangle(n,root,i,j,sign):
    unit=lambda v:tuple(int(v==k) for k in range(n))
    zero=(0,)*n;u=tuple(sign*x for x in sub(unit(i),unit(root)));v=tuple(sign*x for x in sub(unit(j),unit(root)))
    vertices=(zero,u,v);out=[]
    for a,b,c in ((0,1,1),(1,2,1),(0,2,-1)):
        head=vertices[a];edge=sub(vertices[b],head)
        if edge.index(1)<edge.index(-1):head=vertices[b];edge=tuple(-x for x in edge);c=-c
        out.append((head,edge,c))
    return out


def chain(n,root,left_edges,right_edges):
    factors=[triangle(n,root,*edge,sign) for sign,edges in ((1,left_edges),(-1,right_edges)) for edge in edges]
    out=defaultdict(int)
    for terms in product(*factors):
        head=(0,)*n;edges=[];coefficient=1
        for h,e,c in terms:head=add(head,h);edges.append(e);coefficient*=c
        if len(set(edges))<len(edges):continue
        coefficient*=(-1)**sum(edges[i]>edges[j] for i in range(len(edges)) for j in range(i+1,len(edges)))
        out[(head,tuple(sorted(edges)))]+=coefficient
    return {k:v for k,v in out.items() if v}


def boundary(cubes):
    out=defaultdict(int)
    for (head,edges),c in cubes.items():
        for j,e in enumerate(edges):
            rest=edges[:j]+edges[j+1:];sign=(-1)**j*c
            out[(add(head,e),rest)]+=sign;out[(head,rest)]-=sign
    return {k:v for k,v in out.items() if v}


def plane(head,edges,n):
    columns=[head]+list(edges);matrix=sp.Matrix(columns)
    if matrix.rank()<n-2:return None
    augmented=matrix.col_join(sp.Matrix([[1]+[0]*(n-1)]))
    basis=augmented.nullspace();assert len(basis)==1
    values=list(basis[0]);den=sp.ilcm(*(v.q for v in values));values=[int(v*den) for v in values]
    common=math.gcd(*values);values=[v//common for v in values]
    if next(v for v in values if v)<0:values=[-v for v in values]
    return tuple(values)


def main():
    start=time.monotonic();records=[]
    for n,left,right in ((5,[(1,2)],[(3,4)]),(6,[(1,2)],[(3,4),(4,5)])):
        cubes=chain(n,0,left,right);assert not boundary(cubes);groups=defaultdict(list);lower=[]
        for (head,edges),c in cubes.items():
            key=plane(head,edges,n);item=dict(head=head,edges=edges,coefficient=c)
            if key is None:lower.append(item)
            else:groups[key].append(item)
        facet_planes={(0,)+(1,)*(n-1)}|{tuple(int(i==j) for i in range(n)) for j in range(1,n)}
        exceptional={key:items for key,items in groups.items() if key not in facet_planes}
        singleton=[(key,items[0]) for key,items in exceptional.items() if len(items)==1]
        rec=dict(n=n,left_edges=left,right_edges=right,cubes=len(cubes),lower_dimensional=len(lower),
                 span_groups=[dict(normal=k,cubes=v,facet=k in facet_planes) for k,v in sorted(groups.items())],
                 singleton_nonfacet_obstructions=[dict(normal=k,cube=v) for k,v in singleton],
                 status='EXACT_SINGLETON_NONFACET_OBSTRUCTION' if singleton else 'SPAN_GROUPS_REQUIRE_TOP_CLASS_CHECK')
        records.append(rec);print('N',n,'CUBES',len(cubes),'PLANES',len(groups),'NONFACET',len(exceptional),'SINGLETONS',len(singleton),flush=True)
    out=dict(status='GHOST_ROOT_TRIANGLE_PRODUCT_CONTROL',records=records,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
             scope='Tests only the displayed product cycles; a singleton full-dimensional nonfacet span refutes its being proportional to the simplex boundary.')
    (HERE/'overnight_upper_triangle_product.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
