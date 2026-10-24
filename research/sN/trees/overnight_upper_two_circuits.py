#!/usr/bin/env python3
"""Two disjoint positive circuits, one mean bridge, and independent leaves."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import json
import math
import random
import sys
import time

from flint import fmpq_mat
from overnight_upper_star_heads import histograms
from overnight_upper_probe import digest
from rational_identity import Verifier,add

HERE=Path(__file__).parent
H=(-1,0,1);CH=(0,1,2);D=(-1,0,1)


def family(n):
    keys=[]
    for s in range(1,n-1):
        for t in range(1,n-s):
            for hs in histograms(s,3):
                if not hs[0]:continue
                for ht in histograms(t,3):
                    if not ht[0]:continue
                    for hl in histograms(n-1-s-t,3):
                        for delta in D:keys.append((s,t,hs,ht,hl,delta))
    out={key:[] for key in keys}
    for a in range(n):
        other=[i for i in range(n) if i!=a]
        for s in range(1,n-1):
            for S in combinations(other,s):
                rest=[i for i in other if i not in S]
                for t in range(1,len(rest)+1):
                    for T in combinations(rest,t):
                        leaves=[i for i in rest if i not in T]
                        for cs in product(CH,repeat=s):
                            if min(cs):continue
                            hs=tuple(cs.count(v) for v in CH)
                            for ct in product(CH,repeat=t):
                                if min(ct):continue
                                ht=tuple(ct.count(v) for v in CH)
                                for cl in product(H,repeat=len(leaves)):
                                    hl=tuple(cl.count(v) for v in H);h=[0]*n
                                    for i,v in zip(S+T+tuple(leaves),cs+ct+cl):h[i]=v
                                    for delta in D:out[s,t,hs,ht,hl,delta].append((a,S,T,tuple(h),delta))
    return keys,[out[key] for key in keys]


def atom_value(n,unit,j,k,p):
    a,S,T,h,delta=unit;aa=p[a];bridge=sum(p[i] for i in S)+aa*delta
    den=bridge*(bridge+aa)
    for i in range(n):
        if i in (a,j,k):continue
        q=p[i]+aa*h[i]
        if i in S:q-=p[j]+aa*h[j]
        elif i in T:q-=p[k]+aa*h[k]
        den*=q*(q+aa)
    return Q(len(S)*len(T)*(-aa)**(n-4),den)


def values(n,columns,p):
    row=[]
    for col in columns:
        v=Q(0)
        for unit in col:
            for j in unit[1]:
                for k in unit[2]:v+=atom_value(n,unit,j,k,p)
        row.append(v)
    return row+[Q((-1)**(n-1),math.prod(p))]


def expression(n,columns,coefficients,target):
    fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
    out=defaultdict(Q)
    for coeff,col in zip(coefficients,columns):
        if not coeff:continue
        for a,S,T,h,delta in col:
            aa=fs[a];bridge=tuple(sum(fs[i][v] for i in S)+delta*aa[v] for v in range(n))
            for j in S:
                for k in T:
                    den=[(bridge,1),(tuple(x+y for x,y in zip(bridge,aa)),1)]
                    for i in range(n):
                        if i in (a,j,k):continue
                        q=tuple(x+h[i]*z for x,z in zip(fs[i],aa))
                        r=j if i in S else k if i in T else None
                        if r is not None:q=tuple(x-y-h[r]*z for x,y,z in zip(q,fs[r],aa))
                        den.extend([(q,1),(tuple(x+z for x,z in zip(q,aa)),1)])
                    add(out,coeff*len(S)*len(T),tuple(-x for x in aa),n-4,den)
    if target:add(out,-((-1)**(n-1)),(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
    return out


def coordinate_value(n,unit,p):
    a,S,T,h,delta=unit;idx=[i for i in range(n) if i!=a]
    ms=[Q(int(i in S),len(S)) for i in range(n)];mt=[Q(int(i in T),len(T)) for i in range(n)]
    bridge=[x-y for x,y in zip(ms,mt)]
    gs={j:[Q(int(i==j))-(ms[i] if j in S else mt[i]) for i in range(n)] for j in idx}
    head=[mt[i]-int(i==a)+delta*bridge[i]+sum(h[j]*gs[j][i] for j in idx) for i in range(n)]
    value=Q(0)
    for j in S:
        for k in T:
            A=fmpq_mat([[str(v[i]) for i in idx] for v in [head,bridge]+[gs[l] for l in idx if l not in (j,k)]])
            det=abs(Q(str(A.det())));assert det==Q(1,len(S)*len(T))
            cov=A.transpose().inv()*fmpq_mat([[p[i]] for i in idx]);w=[Q(str(cov[i,0])) for i in range(n-1)]
            assert w[0]==-p[a];term=w[0]**(n-4)/det
            for z in w[1:]:term/=z*(z-w[0])
            assert term==atom_value(n,unit,j,k,p);value+=term
    return value


def main(n):
    started=time.monotonic();keys,columns=family(n);width=len(columns)
    print('FAMILY',n,'COLUMNS',width,'UNITS',sum(map(len,columns)),flush=True)
    rng=random.Random(24102493+n);rows=[];points=[]
    while len(rows)<width+10:
        p=[rng.randrange(1,1000) for _ in range(n-1)];p.append(-sum(p))
        try:row=values(n,columns,p)
        except ZeroDivisionError:continue
        rows.append(row);points.append(p)
        if len(rows)%10==0:print('ROWS',len(rows),'SECONDS',time.monotonic()-started,flush=True)
    rr,rank=fmpq_mat([[str(q) for q in r] for r in rows]).rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,head_values=H,core_head_values=CH,bridge_parameters=D,
              orbit_keys=keys,unit_count=sum(map(len,columns)),points=points,
              rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target),rank],
              producer_sha256=digest(Path(__file__)))
    print('EXACT RANKS',data['ranks'],'SECONDS',time.monotonic()-started,flush=True)
    independent=[sum((coordinate_value(n,u,points[0]) for u in col),Q(0)) for col in columns]
    assert independent==rows[0][:-1];data['independent_coordinate_full_rows']=1
    path=HERE/f'overnight_upper_two_circuits_{n}.json';path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            assert V.check(expression(n,columns,cs,False))
            vectors.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='EXACT_TWO_CIRCUIT_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=vectors,
                    exact_kernel_count=len(vectors),ordinary_rank_upper=width-len(vectors))
    else:
        cs=[Q(0)]*width
        for i,j in enumerate(pivots):cs[j]=Q(str(rr[i,width]))
        data['coefficients']=list(map(str,cs));path.write_text(json.dumps(data,separators=(',',':'))+'\n')
        assert V.check(expression(n,columns,cs,True));data['status']='EXACT_TOP_IDENTITY'
    data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]))
