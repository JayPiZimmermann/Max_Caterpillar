"""Exact all-apex complete paired-cut residue recurrence, bounded controls.

Direct side: normalized heads and positive-endpoint cuts, all permutations.
Recursion side: deletion of a leaf or a pendant pair and smaller rooted kernels.
No stored residue values or interpolation are used.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time
from dfs_review_fourier import family
HERE=Path(__file__).parent

def adj(unit):
    V={v for e in unit['edges'] for v in e};A={v:set()for v in V}
    for u,v in unit['edges']:A[u].add(v);A[v].add(u)
    return A

def normalized(unit):
    A=adj(unit);h={v:0 for v in A};h[0]=-1;h[unit['root']]+=1;out=[]
    for u,v in unit['edges']:
        if u>v:h[u]+=1;h[v]-=1
    for edge in unit['edges']:
        u,v=sorted(edge);C={u};todo=[u]
        for x in todo:
            for y in A[x]:
                if {x,y}=={u,v}:continue
                if y not in C:C.add(y);todo.append(y)
        out.append((C,sum(h[x]for x in C)))
    return out

def direct(unit,z,eta):
    n=len(eta)+2;labels=[0]+sorted(adj(unit));base=[z,-z]+list(eta);slope=[0,-1]+[0]*(len(eta)-1)+[1];factors=normalized(unit);total=Q(0);hits=0
    for p in itertools.permutations(range(n)):
        b=dict(zip(labels,[base[i]for i in p]));d=dict(zip(labels,[slope[i]for i in p]));den=1;zero=[]
        for C,H in factors:
            q=sum(b[v]for v in C);t=sum(d[v]for v in C)
            for off in(H,H+1):
                c=q+off*b[0];s=t+off*d[0]
                if c:den*=c
                else:assert s;zero.append(s)
        assert len(zero)<=1
        if zero:total+=Q((-b[0])**(n-4),den*zero[0]);hits+=1
    return total,hits

def rooted_kernel(unit,omega):
    A=adj(unit);r=unit['root'];parent={r:None};order=[r]
    for v in order:
        for w in A[v]:
            if w!=parent[v]:parent[w]=v;order.append(w)
    sums=dict(omega);E=set(map(tuple,unit['edges']));den=1;a=omega[0]
    for v in reversed(order[1:]):
        p=parent[v];q=sums[v];sgn=1 if(v,p)in E else -1;den*=q*(q+sgn*a);sums[p]+=q
    assert den
    exponent=len(A)-3
    return Q((-a)**exponent,den)if exponent>=0 else Q(1,den*(-a)**(-exponent))

def smaller(unit,drop,root):return {'root':root,'edges':[e for e in unit['edges']if not(set(e)&set(drop))]}

def recurrence(unit,z,eta):
    A=adj(unit);r=unit['root'];E=set(map(tuple,unit['edges']));leaf_total=Q(0);pair_total=Q(0);pieces=[]
    for v in A:
        if len(A[v])!=1:continue
        h=next(iter(A[v]));coef=(1 if(h,v)in E else -1)if v==r else(1 if(v,h)in E else 0)
        if not coef:continue
        U=smaller(unit,{v},h if v==r else r);V=sorted(adj(U));value=Q(0)
        for p in itertools.permutations(eta):
            om=dict(zip(V,p))
            for a in(z,-z):
                w=dict(om);w[0]=a;w[h]-=a;value-=coef*rooted_kernel(U,w)
        leaf_total+=value;pieces.append({'kind':'outlier-apex leaf','leaf':v,'value':str(value)})
    for v,w in itertools.combinations(A,2):
        if w not in A[v]:continue
        C={v,w};boundary=[(x,y)for x in C for y in A[x]if y not in C]
        if len(boundary)!=1:continue
        hub,h=boundary[0];root_inside=r in C
        eps=1 if((h,hub)if root_inside else(hub,h))in E else -1
        if root_inside and eps<0:continue
        exceptional=root_inside and r!=hub and(r,hub)in E
        U=smaller(unit,C,h if root_inside else r);labels=[0]+sorted(adj(U));value=Q(0)
        for p in itertools.permutations(eta):
            om=dict(zip(labels,p));a=om[0];coef=Q(-2*eps*a,z*z-a*a)
            if exceptional:coef=Q(-2*a*(z*z+2*a*a),(z*z-a*a)*(z*z-4*a*a))
            value+=coef*rooted_kernel(U,om)
        pair_total+=value;pieces.append({'kind':'finite-apex pendant pair','pair':sorted(C),'exceptional_root_leaf':exceptional,'value':str(value)})
    return leaf_total+pair_total,pieces

def main():
    start=time.monotonic();cases=[(u,5)for u in family(5,'all')]
    for E in [[(1,2),(2,3),(3,4),(4,5),(5,6)],[(2,1),(3,2),(4,3),(5,4),(6,5)],[(1,2),(3,2),(4,3),(5,2),(6,5)],[(2,1),(2,3),(3,4),(2,5),(5,6)]]:cases.append(({'root':1,'edges':E},7))
    rows=[]
    for u,n in cases:
        p=[3**i for i in range(n-3)];eta=p+[-sum(p)];z=10*sum(p)+7;lhs,hits=direct(u,z,eta);rhs,pieces=recurrence(u,z,eta);assert lhs==rhs,(u,lhs,rhs)
        rows.append({'arity':n,'unit':{k:v for k,v in u.items()if k!='cuts'},'z':z,'eta':eta,'value':str(lhs),'pole_summands':hits,'pieces':pieces})
    result={'status':'EXACT_ALL_APEX_CUT_RESIDUE_RECURRENCE_CONTROLS_PASS','cases':rows,'seconds':time.monotonic()-start,'scope':'Exact controls and general termwise derivation. Recurrence retains external-apex shifts and the exceptional root-leaf factor z²−4a²; it is not an all-tree separator.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(rows),result['seconds'],flush=True)
if __name__=='__main__':main()
