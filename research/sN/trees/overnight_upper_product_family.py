#!/usr/bin/env python3
"""Dihedral top-boundary probe for NC ghost-root triangle product cycles.

No head alphabet is enumerated. Each column is an automatically closed
product cycle from a two-component NC forest. A uniform boundary identity
in this exponentially sized family would permit one augmentation/filling
step, avoiding a factorial facet recursion. Small controls only here.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations,product
from pathlib import Path
import hashlib,json,math,random,sys,time
from flint import fmpq_mat,nmod_mat,ctx

HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import term,Verifier
ctx.threads=1;PRIME=1000003


def components(n,edges):
    parent=list(range(n))
    def root(v):
        while parent[v]!=v:v=parent[v]
        return v
    for u,v in edges:
        a,b=root(u),root(v)
        if a==b:return None
        parent[a]=b
    out=defaultdict(list)
    for v in range(n):out[root(v)].append(v)
    return sorted(out.values())


def crosses(e,f):
    a,b=sorted(e);c,d=sorted(f);return a<c<b<d or c<a<d<b


def group(n):
    return [tuple((sign*i+shift)%n for i in range(n)) for sign in (1,-1) for shift in range(n)]


def parity(pi):return (-1)**sum(pi[i]>pi[j] for i in range(len(pi)) for j in range(i+1,len(pi)))
def addv(a,b):return tuple(x+y for x,y in zip(a,b))
def diff(n,i,j):return tuple(int(k==i)-int(k==j) for k in range(n))


def normalize_cube(h,edges,c):
    out=[]
    for v in edges:
        if v.index(1)<v.index(-1):h=addv(h,v);v=tuple(-x for x in v);c=-c
        out.append(v)
    if len(set(out))<len(out):return None
    c*=(-1)**sum(out[i]>out[j] for i in range(len(out)) for j in range(i+1,len(out)))
    return (h,tuple(sorted(out))),c


def triangle(n,r,i,j,sign):
    zero=(0,)*n;u=tuple(sign*x for x in diff(n,i,r));v=tuple(sign*x for x in diff(n,j,r))
    return [(zero,u,1),(u,tuple(y-x for x,y in zip(u,v)),1),(zero,v,-1)]


def raw_chain(n,descriptor):
    root,positive,edges=descriptor;positive=set(positive)
    factors=[triangle(n,root,u,v,1 if u in positive else -1) for u,v in edges]
    out=defaultdict(Q)
    for choices in product(*factors):
        h=(0,)*n;c=1;vectors=[]
        for base,vector,coefficient in choices:h=addv(h,base);vectors.append(vector);c*=coefficient
        item=normalize_cube(h,vectors,c)
        if item:out[item[0]]+=item[1]
    return {k:v for k,v in out.items() if v}


def sym_chain(n,descriptor):
    chain=raw_chain(n,descriptor);out=defaultdict(Q)
    for pi in group(n):
        def permute(v):
            w=[0]*n
            for i,x in enumerate(v):w[pi[i]]=x
            return tuple(w)
        for (h,edges),c in chain.items():
            item=normalize_cube(permute(h),[permute(v) for v in edges],c*parity(pi))
            if item:out[item[0]]+=item[1]
    return {k:v for k,v in out.items() if v}


def family(n):
    reps=set();raw=0
    for ghost in range(n):
        verts=[i for i in range(n) if i!=ghost]
        for edges in combinations(list(combinations(verts,2)),n-3):
            if any(crosses(e,f) for e,f in combinations(edges,2)):continue
            comp=components(n,edges)
            if comp is None or len(comp)!=3:continue
            comp=[tuple(c) for c in comp if c!=[ghost]]
            if len(comp)!=2:continue
            for positive in comp:
                raw+=1;keys=[]
                for pi in group(n):keys.append((pi[ghost],tuple(sorted(pi[v] for v in positive)),tuple(sorted(tuple(sorted((pi[u],pi[v]))) for u,v in edges))))
                reps.add(min(keys))
    return sorted(reps),raw


@lru_cache(None)
def cube_kernel(key):
    h,edges=key;n=len(h);d=n-2
    graph=[(v.index(1),v.index(-1)) for v in edges];comp=components(n,graph)
    if comp is None or len(comp)!=3:return None
    first=next(c for c in comp if 0 in c);other=[c for c in comp if c is not first]
    a,b=(sum(h[i] for i in c) for c in other)
    if a==b==0:return None
    normal=[0]*n
    for i in other[0]:normal[i]=b
    for i in other[1]:normal[i]=-a
    common=math.gcd(*normal);normal=[v//common for v in normal]
    if next(v for v in normal if v)<0:normal=[-v for v in normal]
    drop=next(i for i,v in enumerate(normal) if v);indices=[i for i in range(n) if i not in (0,drop)]
    columns=[h]+list(edges);B=fmpq_mat([[v[i] for v in columns] for i in indices]);det=Q(str(B.det()));assert det
    inv=B.inv();adj=[tuple(int(Q(str(inv[i,j]))*det) for j in range(d)) for i in range(d)]
    numerator=adj[0]+(0,);den=[]
    for row in adj[1:]:den.extend([(row+(0,),1),(tuple(x-y for x,y in zip(row,adj[0]))+(0,),1)])
    normalized=term(det**d,numerator,d-3,den)
    return tuple(normal),normalized


def expression(chain):
    out=defaultdict(lambda:defaultdict(Q))
    for key,c in chain.items():
        got=cube_kernel(key)
        if got is not None:
            plane,(monomial,coefficient)=got;out[plane][monomial]+=c*coefficient
    return {p:{k:v for k,v in e.items() if v} for p,e in out.items() if any(e.values())}


def target(n):
    d=n-2;out={}
    for missing in range(n):
        normal=(0,)+(1,)*(n-1) if missing==0 else tuple(int(i==missing) for i in range(n))
        drop=next(i for i,v in enumerate(normal) if v);indices=[i for i in range(n) if i not in (0,drop)]
        facet=[i for i in range(n) if i!=missing];columns=[diff(n,i,facet[0]) for i in facet[1:]]
        B=fmpq_mat([[v[i] for v in columns] for i in indices]);det=Q(str(B.det()));inv=B.inv()
        adj=[tuple(int(Q(str(inv[i,j]))*det) for j in range(d)) for i in range(d)]
        forms=[tuple(-sum(row[j] for row in adj) for j in range(d))]+adj
        monomial,c=term((-1)**(missing+d)*det**d,(0,)*d+(1,),0,[(f+(0,),1) for f in forms]);out[normal]={monomial:c}
    return out


def evaluate(expr,point,p=PRIME):
    total=0
    for (num,k,den),c in expr.items():
        val=(c.numerator*pow(c.denominator,-1,p))%p
        val=val*pow((sum(a*b for a,b in zip(num[:-1],point))+num[-1])%p,k,p)%p
        for f,power in den:
            q=(sum(a*b for a,b in zip(f[:-1],point))+f[-1])%p
            if not q:raise ZeroDivisionError
            val=val*pow(pow(q,power,p),-1,p)%p
        total=(total+val)%p
    return total


def ratrec(v,p):
    r0,r1,t0,t1=p,v,0,1;limit=math.isqrt(p//2)
    while abs(r1)>limit:
        q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
    if not t1 or abs(t1)>limit:return None
    c=Q(r1,t1);return c if (c.numerator-v*c.denominator)%p==0 else None


def main(n):
    started=time.monotonic();control=expression(raw_chain(5,(0,(1,2),((1,2),(3,4)))));expected=target(5);verifier=Verifier(20)
    for plane in set(control)|set(expected):
        e=defaultdict(Q,control.get(plane,{}))
        for k,c in expected.get(plane,{}).items():e[k]-=c
        assert verifier.check(e),'N5 product/target convention control'
    reps,raw=family(n);print('INVENTORY',n,'RAW',raw,'DIHEDRAL',len(reps),flush=True)
    columns=[];descriptors=[];seen=set()
    for descriptor in reps:
        expr=expression(sym_chain(n,descriptor))
        if not expr:continue
        signature=tuple((p,tuple(sorted(e.items()))) for p,e in sorted(expr.items()))
        if signature in seen:continue
        seen.add(signature);descriptors.append(descriptor);columns.append(expr)
    wanted=target(n);planes=sorted(set(wanted)|{p for e in columns for p in e});print('COLUMNS',len(columns),'PLANES',len(planes),'CUBES',cube_kernel.cache_info().currsize,'SECONDS',time.monotonic()-started,flush=True)
    rng=random.Random(251027);rows=[];points=[]
    for plane in planes:
        accepted=0
        while accepted<4:
            point=tuple(rng.randrange(1,1000) for _ in range(n-2))
            try:row=[evaluate(e.get(plane,{}),point) for e in columns]+[evaluate(wanted.get(plane,{}),point)]
            except ZeroDivisionError:continue
            rows.append(row);points.append((plane,point));accepted+=1
    rr,rank=nmod_mat(rows,PRIME).rref();width=len(columns);pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)]
    augmented=width in pivots;ranks=[rank-int(augmented),rank]
    record=dict(status='MODULAR_PRODUCT_FAMILY_BOUNDARY_DIAGNOSTIC',n=n,raw_products=raw,dihedral_representatives=len(reps),
                descriptors=descriptors,planes=planes,prime=PRIME,points=points,modular_rows=rows,ranks=ranks,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
    print('RANKS',ranks,'SECONDS',record['seconds'],flush=True)
    if not augmented:
        coefficients=[Q(0)]*width
        for i,j in enumerate(pivots):coefficients[j]=ratrec(int(rr[i,width]),PRIME)
        if all(c is not None for c in coefficients):
            record['candidate_coefficients']=list(map(str,coefficients));gate=Verifier(240);passed=[]
            for plane in planes:
                expr=defaultdict(Q)
                for c,col in zip(coefficients,columns):
                    if c:
                        for key,v in col.get(plane,{}).items():expr[key]+=c*v
                for key,v in wanted.get(plane,{}).items():expr[key]-=v
                if not gate.check(expr):break
                passed.append(plane)
            record['exact_planes_passed']=passed
            if len(passed)==len(planes):record['status']='EXACT_PRODUCT_FAMILY_BOUNDARY_IDENTITY'
    elif rank==width+1:record['status']='EXACT_FULL_COLUMN_PRODUCT_FAMILY_OBSTRUCTION'
    record['seconds']=time.monotonic()-started
    (HERE/f'overnight_upper_product_family_{n}.json').write_text(json.dumps(record,separators=(',',':'))+'\n')
    print('DONE',record['status'],'SECONDS',record['seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]) if len(sys.argv)>1 else 6)
