#!/usr/bin/env python3
"""Graphic zonotope facets and coherent spanning-forest tiles.

For each full-rank unit sigma(h+sum sigma(edge)), sum the pyramids over
facets visible from0. Each facet is tiled by graphic bases with the exact
translation determined by a generic lifting. All calculations are integral.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations,product
import math
from flint import fmpq_mat

def diff(n,u,v):return tuple(int(i==u)-int(i==v) for i in range(n))
def addv(a,b):return tuple(x+y for x,y in zip(a,b))

def components(n,edges):
    p=list(range(n))
    def find(v):
        while p[v]!=v:v=p[v]
        return v
    for u,v in edges:
        a,b=find(u),find(v)
        if a==b:return None
        p[a]=b
    groups=defaultdict(list)
    for v in range(n):groups[find(v)].append(v)
    return sorted(tuple(v) for v in groups.values())

def connected(vertices,edges):
    if len(vertices)==1:return True
    adjacency={v:[] for v in vertices}
    for u,v in edges:
        if u in adjacency and v in adjacency:adjacency[u].append(v);adjacency[v].append(u)
    seen={min(vertices)};stack=list(seen)
    while stack:
        for v in adjacency[stack.pop()]:
            if v not in seen:seen.add(v);stack.append(v)
    return seen==set(vertices)

@lru_cache(None)
def facets(n,graph):
    """All ordered facets S, with support vector and independent tiles."""
    answer=[]
    for mask in range(1,(1<<n)-1):
        S={i for i in range(n) if mask>>i&1};P=set(range(n))-S
        if not connected(S,graph) or not connected(P,graph):continue
        free=[e for e in graph if (e[0] in S)==(e[1] in S)]
        cross=[e for e in graph if e[0] in S and e[1] not in S]
        fixed=tuple(sum(int(i==u)-int(i==v) for u,v in cross) for i in range(n))
        tiles=[]
        for basis in combinations(free,n-2):
            comps=components(n,basis)
            if comps is None or {frozenset(c) for c in comps}!={frozenset(S),frozenset(P)}:continue
            # Expose a lower facet of the lifted zonotope. Distinct powers
            # of2 give a nonzero signed sum on every graphic circuit.
            potential={}
            for comp in comps:
                potential[min(comp)]=0
                while not set(comp)<=potential.keys():
                    for u,v in basis:
                        height=1<<graph.index((u,v))
                        if u in potential and v not in potential:potential[v]=potential[u]-height
                        elif v in potential and u not in potential:potential[u]=potential[v]+height
            shift=[0]*n
            for u,v in free:
                if (u,v) in basis:continue
                slack=potential[u]-potential[v]-(1<<graph.index((u,v)))
                assert slack
                if slack>0:shift[u]+=1;shift[v]-=1
            tiles.append((tuple(shift),basis))
        assert tiles
        answer.append((mask,fixed,tuple(tiles)))
    return tuple(answer)

@lru_cache(None)
def cuts(n,basis,mask):
    S={i for i in range(n) if mask>>i&1};P=set(range(n))-S
    roots={min(S),min(P)}
    adjacency={v:[] for v in range(n)}
    for u,v in basis:adjacency[u].append(v);adjacency[v].append(u)
    result=[]
    for u,v in basis:
        # Explicit DFS with the chosen edge removed.
        seen={u};stack=[u]
        while stack:
            current=stack.pop()
            for nxt in adjacency[current]:
                if {current,nxt}=={u,v} or nxt in seen:continue
                seen.add(nxt);stack.append(nxt)
        whole=S if u in S else P
        away=seen if not seen&roots else whole-seen
        epsilon=1 if u in away else -1
        result.append((tuple(sorted(away)),epsilon))
    return tuple(result)

def atoms(n,graph,head):
    answer=[]
    for mask,fixed,tiles in facets(n,graph):
        S=tuple(i for i in range(n) if mask>>i&1)
        face_head=addv(head,fixed);height=sum(face_head[i] for i in S)
        if height>=0:continue
        c=-height
        for shift,basis in tiles:
            h=addv(face_head,shift)
            factors=[]
            for away,epsilon in cuts(n,basis,mask):
                H=sum(h[i] for i in away)
                # Clear c from q+(a/c)H in both factors. The resulting
                # scalar c^(N-1) is recorded separately.
                for t in (H,H+epsilon):
                    factors.append(tuple(c*int(i in away)+t*int(i in S) for i in range(n)))
            numerator=tuple(-int(i in S) for i in range(n))
            answer.append((c**(n-1),numerator,tuple(factors)))
    return tuple(answer)

def evaluate_atoms(n,items,point):
    value=Q(0)
    dot=lambda f:sum(x*y for x,y in zip(f,point))
    for coefficient,numerator,denominator in items:
        d=math.prod(dot(f) for f in denominator)
        if not d:raise ZeroDivisionError
        num=Q(dot(numerator))**(n-4)
        value+=coefficient*num/d
    return value

def vertices(n,graph,head=None):
    head=head or (0,)*n
    return sorted({tuple(head[i]+sum(bit*(int(i==u)-int(i==v)) for bit,(u,v) in zip(bits,graph))
                         for i in range(n)) for bits in product((0,1),repeat=len(graph))})

def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))

def polygon(points):
    """Exact two-dimensional convex hull, counterclockwise."""
    points=sorted(set(points))
    def turn(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    lower=[]
    for p in points:
        while len(lower)>1 and turn(lower[-2],lower[-1],p)<=0:lower.pop()
        lower.append(p)
    upper=[]
    for p in reversed(points):
        while len(upper)>1 and turn(upper[-2],upper[-1],p)<=0:upper.pop()
        upper.append(p)
    return lower[:-1]+upper[:-1]

def direct_facets_3d(points):
    """Brute exact facets from vertex triples; independent of graph cuts."""
    facets={}
    for a,b,c in combinations(points,3):
        normal=cross(sub(b,a),sub(c,a))
        if not any(normal):continue
        g=math.gcd(*normal);normal=tuple(x//g for x in normal);height=dot(normal,a)
        offsets=[dot(normal,p)-height for p in points]
        if all(v<=0 for v in offsets):pass
        elif all(v>=0 for v in offsets):normal=tuple(-x for x in normal);height=-height
        else:continue
        facets[(normal,height)]=tuple(p for p in points if dot(normal,p)==height)
    return facets

def direct_kernel_4(graph,head,point):
    """Independently triangulate visible facets into actual tetrahedra."""
    points=[v[1:] for v in vertices(4,graph,head)]
    result=Q(0)
    for (normal,height),face in direct_facets_3d(points).items():
        if height>=0:continue
        drop=next(i for i,c in enumerate(normal) if c)
        indices=[i for i in range(3) if i!=drop]
        projection={tuple(p[i] for i in indices):p for p in face}
        hull=polygon(projection)
        for i in range(1,len(hull)-1):
            triangle=[projection[hull[j]] for j in (0,i,i+1)]
            B=fmpq_mat([[p[j] for p in triangle] for j in range(3)])
            det=Q(str(B.det()));assert det
            inv=B.inv()
            omega=[sum(Q(str(inv[i,j]))*point[j+1] for j in range(3)) for i in range(3)]
            denominator=sum(omega)*math.prod(omega)
            if not denominator:raise ZeroDivisionError
            result+=1/(abs(det)*denominator)
    return result
