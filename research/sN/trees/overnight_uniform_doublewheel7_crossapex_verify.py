#!/usr/bin/env python3
"""Independent rooted-cut arithmetic for cross-apex residues and edge splitting.

No producer imports. The frequency chart is evaluated first, then every term
is a rational function of two normal coordinates. Rooted cuts and their edge
signs replace the producer's positive-endpoint component coordinates.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib,json,math,time

UNITS=[(1,((1,2),(1,3),(1,4),(5,2),(6,2))),
       (1,((1,2),(1,3),(4,2),(5,2),(6,2)))]


def cuts(root,edges):
    adjacency={root:[]}
    for u,v in edges:adjacency.setdefault(u,[]).append(v);adjacency.setdefault(v,[]).append(u)
    parent={root:None};order=[root]
    for v in order:
        for w in adjacency[v]:
            if w!=parent[v]:assert w not in parent;parent[w]=v;order.append(w)
    descendants={v:{v}for v in order}
    out=[]
    for v in reversed(order[1:]):
        out.append((v,parent[v],descendants[v],1 if(v,parent[v])in edges else-1))
        descendants[parent[v]]|=descendants[v]
    return out


def cross_chart(size):
    a=Q(1);free=iter((10,100,1000));frequency=[(a,0,0)];total=Q(0)
    for _ in range(size-1):
        value=Q(next(free));frequency.append((value,0,0));total+=value
    frequency.append((a-total,-1,0))
    frequency.append((a,-1,1))
    while len(frequency)<6:frequency.append((Q(next(free)),0,0))
    frequency.append(tuple(-sum(f[i]for f in frequency)for i in range(3)))
    return frequency


def residue(root,edges,frequency,order):
    rooted=cuts(root,edges);total=Q(0)
    for perm in permutations(range(7)):
        omega=[frequency[i]for i in perm];a=omega[0];forms=[]
        for _,_,side,epsilon in rooted:
            q=tuple(sum(omega[v][j]for v in side)for j in range(3))
            forms.extend((q,tuple(q[j]+epsilon*a[j]for j in range(3))))
        zero=[f for f in forms if not f[0]]
        assert len(zero)<=2 and a[0]
        if len(zero)!=2:continue
        first=[f for f in zero if f[2-order]==0]
        if not first:continue
        assert len(first)==1
        second=zero[1]if first[0]==zero[0]else zero[0]
        denominator=first[0][1+order]*second[2-order]*math.prod(f[0]for f in forms if f[0])
        assert denominator
        total+=(-a[0])**3/denominator
    return total


def kernel(root,edges,omega,a):
    assert sum(omega.values())==-a
    value=Q(-a)**(len(edges)-2)
    for _,_,side,epsilon in cuts(root,edges):
        q=sum(omega[v]for v in side);assert q and q+epsilon*a
        value/=q*(q+epsilon*a)
    return value


def edge_factorizations():
    controls=[]
    for root,edges in UNITS:
        vertices=set(range(1,7))
        for child,hub,C,epsilon in cuts(root,edges):
            if epsilon!= -1:continue
            D=vertices-C;omega={v:Q(3**v)for v in vertices}
            a=sum(omega[v]for v in C)
            omega[root]=-2*a-sum(omega[v]for v in D if v!=root)
            old=Q(-a)**3/a
            for v,p,side,e in cuts(root,edges):
                if v==child:continue
                q=sum(omega[j]for j in side);assert q and q+e*a
                old/=q*(q+e*a)
            inner=tuple((v,u)for u,v in edges if u in C and v in C)
            outer=tuple((u,v)for u,v in edges if u in D and v in D)
            fC={v:omega[v]for v in C};fD={v:omega[v]+(a if v==hub else 0)for v in D}
            product=(-1)**len(C)*a*a*kernel(child,inner,fC,-a)*kernel(root,outer,fD,a)
            assert old==product
            controls.append(dict(root=root,edges=edges,child=child,hub=hub,detached_size=len(C),residue=str(old)))
    return controls


def main():
    started=time.monotonic();rows=[]
    expected={3:Q(-5512019473,137054472797038500000),4:Q(3359973,170816357211500000)}
    for size in(3,4):
        frequency=cross_chart(size)
        for order in(0,1):
            values=[residue(r,e,frequency,order)for r,e in UNITS]
            witness=-3*values[0]+2*values[1]
            assert witness==expected[size]
            rows.append(dict(size=size,order=order,individual_values=list(map(str,values)),witness_value=str(witness)))
    data=dict(status='INDEPENDENT_ROOTED_CUT_CROSS_APEX_AND_SPLITTING_CHECK_PASS',
              rows=rows,inward_edge_factorization_controls=edge_factorizations(),
              seconds=time.monotonic()-started,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Exact controls for the nonzero residue and the displayed general cut-matching proof. Does not claim injectivity of the enlarged residue map.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))


if __name__=='__main__':main()
