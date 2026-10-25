"""Exact N5 controls for an actual normalized four-corner crease functional.

Rational hyperplane-section volumes; SciPy only proposes a triangulation,
whose supporting planes, closed incidence, and volume are checked exactly.
"""
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
from collections import Counter
import itertools,json,math,time
import numpy as np
from scipy.spatial import ConvexHull

HERE=Path(__file__).parent
BASE=[(0,0,1,0,0),(0,1,-1,0,0),(1,-1,0,0,0),
      (0,0,0,0,1),(0,0,0,1,-1),(1,0,0,-1,0)]

def det(v):
    a,b,c=v;return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])

def difference(a,b):return tuple(x-y for x,y in zip(a,b))

@lru_cache(None)
def volume(inequalities):
    vertices=set()
    for rows in itertools.combinations(inequalities,3):
        M=[r[1:]for r in rows];d=det(M)
        if not d:continue
        rhs=[-r[0]for r in rows];p=[]
        for j in range(3):
            A=[list(r)for r in M]
            for i in range(3):A[i][j]=rhs[i]
            p.append(Q(det(A),d))
        if all(r[0]+sum(a*x for a,x in zip(r[1:],p))>=0 for r in inequalities):vertices.add(tuple(p))
    vertices=sorted(vertices)
    if len(vertices)<4:return Q(0)
    if not any(det([difference(v,vertices[0])for v in tri])for tri in itertools.combinations(vertices[1:],3)):return Q(0)
    hull=ConvexHull(np.array([[float(x)for x in v]for v in vertices]));edges=Counter();total=Q(0);o=tuple(sum(v[i]for v in vertices)/len(vertices)for i in range(3));used=set()
    for ids in hull.simplices:
        a,b,c=(vertices[int(i)]for i in ids);cross=[]
        for v in vertices:cross.append(det([difference(b,a),difference(c,a),difference(v,a)]))
        assert all(x>=0 for x in cross)or all(x<=0 for x in cross)
        total+=abs(det([difference(a,o),difference(b,o),difference(c,o)]))/6
        used.update(map(int,ids))
        for i,j in itertools.combinations(map(int,ids),2):edges[tuple(sorted((i,j)))]+=1
    assert all(v==2 for v in edges.values())
    assert len(used)-len(edges)+len(hull.simplices)==2
    return total

def normalize(v):
    g=math.gcd(*v)
    if not g:return tuple(v),0
    if next(x for x in v if x)<0:g=-g
    return tuple(x//g for x in v),abs(g)

def section(n,constraints):
    i=next(i for i,x in enumerate(n)if x);assert n[i]>0;js=[j for j in range(4)if j!=i];rows=set()
    for r in BASE+constraints:
        row=(n[i]*r[0],)+tuple(n[i]*r[j+1]-r[i+1]*n[j]for j in js)
        g=math.gcd(*row)
        if not g:continue
        row=tuple(x//g for x in row)
        if not any(row[1:]):
            if row[0]<0:return Q(0)
            continue
        rows.add(row)
    return volume(tuple(sorted(rows)))

def kappa(n):
    A,B,D,E=n
    if B+E or not B:return 0
    relu=lambda x:max(x,0)
    return relu(A+B)-relu(A)-relu(D)+relu(D-B)

def chart(bits):
    zero=(0,0,0,0);a=(1,0,0,0)if not bits[0]else(-1,1,0,0);b=(0,1,0,0);d=(0,0,1,0)if not bits[1]else(0,0,-1,1);e=(0,0,0,1)
    return [zero,a,b,d,e]

def unit_score(U):
    parts=[]
    for bits in itertools.product((0,1),repeat=2):
        X=chart(bits)
        if U.get('input_sign',1)==-1:X=[tuple(-a for a in row)for row in X]
        head=difference(X[U['root']],X[U.get('apex',0)]);hinges=[difference(X[u],X[v])for u,v in U['edges']];value=Q(0)
        for states in itertools.product((0,1),repeat=len(hinges)):
            L=tuple(head[i]+sum(h[i]for h,s in zip(hinges,states)if s)for i in range(4));n,scale=normalize(L);kap=kappa(n)
            if kap:
                constraints=[(0,)+tuple((1 if s else-1)*x for x in h)for h,s in zip(hinges,states)];den=section(n,[])
                if den:value+=scale*kap*section(n,constraints)/den
        for j,h in enumerate(hinges):
            n,scale=normalize(h);kap=kappa(n)
            if not kap:continue
            rest=[g for i,g in enumerate(hinges)if i!=j];den=section(n,[])
            if not den:continue
            for states in itertools.product((0,1),repeat=len(rest)):
                L=tuple(head[i]+sum(g[i]for g,s in zip(rest,states)if s)for i in range(4));assert any(n[i]*L[k]!=n[k]*L[i]for i in range(4)for k in range(4))
                constraints=[(0,)+tuple((1 if s else-1)*x for x in g)for g,s in zip(rest,states)]+[(0,)+L]
                value+=scale*kap*section(n,constraints)/den
        parts.append(value)
    return parts[0]-parts[1]-parts[2]+parts[3],parts

def main():
    start=time.monotonic();tests=[{'root':1,'edges':[(2,1),(3,1),(4,1)]},
          {'root':1,'edges':[(1,2),(1,3),(1,4)]},
          {'root':2,'edges':[(2,1),(3,1),(4,1)]},
          {'root':2,'edges':[(1,2),(1,3),(1,4)]}];out=[]
    for U in tests:
        value,parts=unit_score(U);row={'unit':U,'score':str(value),'corner_scores':list(map(str,parts))};out.append(row);print(row,'seconds',time.monotonic()-start,flush=True)
    result={'status':'EXACT_NORMALIZED_CREASE_STAR_CONTROLS','rows':out,'volume_cache':str(volume.cache_info()),'scope':'Actual linear functional on CPWL crease measures. These four individual canonical stars are controls only; no symmetrized star-annihilation or matching claim.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
