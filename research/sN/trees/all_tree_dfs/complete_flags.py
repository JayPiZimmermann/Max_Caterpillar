#!/usr/bin/env python3
"""Exact flag invariants for simplex and canonical-root star pyramids.
Producer: research/sN/dfs/h4-general-neurons/venv/bin/python this_file.py 5
All vector/subspace and sign operations use exact rational arithmetic.
No sampling, no head extension, no numerical convex hull. Each key specifies
an iterated exposed-face difference and final segment-width functional.
The invariant kills L_(m-2). This finite test is not a general-m theorem.
"""
from functools import lru_cache
from collections import defaultdict
from itertools import permutations,product
from pathlib import Path
import sys,json,time
import sympy as sp

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
@lru_cache(None)
def space(vs):
    R,piv=sp.Matrix(vs).rref()
    return tuple(tuple(R[i,j] for j in range(R.cols)) for i in range(len(piv)))
def span(vs):return space(tuple(sorted(vs)))
@lru_cache(None)
def normal(W,V):
    B=sp.Matrix(W); A=sp.Matrix(V)*B.T
    ns=A.nullspace();assert len(ns)==1
    u=tuple((B.T*ns[0]))
    c=next(x for x in u if x)
    return tuple(x/c for x in u)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sign(q):assert q;return 1 if q>0 else -1
def extend(out,V,sgn,child):
    for key,val in child.items():out[(V,)+key]+=sgn*val

@lru_cache(None)
def pyramid(h,gs):
    d=len(gs)+1;W=span((h,)+gs);assert len(W)==d
    if d==1:return {():abs(next(v for v in h if v))}
    out=defaultdict(int)
    for j,g in enumerate(gs):
        rest=gs[:j]+gs[j+1:]
        for state in (0,1):
            hh=add(h,g) if state else h
            V=span((hh,)+rest);u=normal(W,V)
            sgn=(2*state-1)*sign(dot(u,g))
            extend(out,V,sgn,pyramid(hh,rest))
    if d==2:
        g=gs[0];V=span((g,));u=normal(W,V)
        extend(out,V,sign(dot(u,h)),{():abs(next(v for v in g if v))})
    return {key:v for key,v in out.items() if v}

@lru_cache(None)
def simplex(vs):
    d=len(vs)-1
    if d==1:return {():abs(next(v for v in sub(vs[1],vs[0]) if v))}
    W=span(tuple(sub(v,vs[0]) for v in vs[1:]));out=defaultdict(int)
    for i,p in enumerate(vs):
        rest=vs[:i]+vs[i+1:]
        V=span(tuple(sub(v,rest[0]) for v in rest[1:]));u=normal(W,V)
        extend(out,V,sign(dot(u,sub(rest[0],p))),simplex(rest))
    return {key:v for key,v in out.items() if v}

def canonical_stars(m):
    e=[tuple(int(i==j) for i in range(m)) for j in range(m)]
    for root in (1,2):
        special=[] if root==1 else [root]
        rest=[v for v in range(2,m) if v!=root]
        for ds in product((0,1),repeat=len(special)):
            for k in range(len(rest)+1):
                dirs=dict(zip(special,ds));dirs.update({v:int(i<k) for i,v in enumerate(rest)})
                gs=tuple(sub(e[v],e[1]) if dirs[v] else sub(e[1],e[v]) for v in range(2,m))
                yield (root,ds,k),sub(e[root],e[0]),gs

def main():
    m=int(sys.argv[1]) if len(sys.argv)>1 else 5
    start=time.time();cols=[];reps=[]
    for name,h,gs in canonical_stars(m):
        out=defaultdict(int)
        for p in permutations(range(m)):
            hh=tuple(h[i] for i in p);gg=tuple(sorted(tuple(g[i] for i in p) for g in gs))
            for key,v in pyramid(hh,gg).items():out[key]+=v
        cols.append({key:v for key,v in out.items() if v});reps.append(name)
        print('orbit',name,'flags',len(cols[-1]),'elapsed',round(time.time()-start,2),flush=True)
    vs=tuple(tuple(int(i==j) for i in range(m)) for j in range(m))
    target=simplex(vs)
    keys=sorted(set(target).union(*(set(c) for c in cols)))
    A=sp.Matrix([[c.get(key,0) for c in cols] for key in keys]);b=sp.Matrix([target.get(key,0) for key in keys])
    rank=A.rank();aug=A.row_join(b).rank()
    print('EXACT',len(keys),'flags',len(cols),'orbits; rank',rank,'with max',aug,flush=True)
    data={'m':m,'reps':reps,'keys':str(keys),'A':[[str(t) for t in A.row(i)] for i in range(A.rows)],'b':[str(t) for t in b],'ranks':[rank,aug]}
    if rank==aug:
        sol,pars=A.gauss_jordan_solve(b);sol=sol.subs({t:0 for t in pars})
        assert A*sol==b
        data['solution']=[str(t) for t in sol];print('witness',list(sol),flush=True)
    else:
        # A short separator uses a row basis of the augmented matrix.
        _,piv=A.row_join(b).T.rref();M=A.row_join(b)[list(piv),:]
        for v in M[:,:-1].T.nullspace():
            q=(v.T*M[:,-1])[0]
            if q:
                v=v/q
                assert v.T*M[:,:-1]==sp.zeros(1,A.cols)
                data['separator']={'rows':list(piv),'weights':[str(t) for t in v]}
                print('separator',data['separator'],flush=True);break
    Path(__file__).with_name(f'complete_flags_{m}.json').write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
