#!/usr/bin/env python3
"""Single positive-circuit cores with independent leaves: exact symmetric test.

All nonapex generators are e_i-mean(core). Core generators have one positive
dependence; outside generators are independent leaves. Core head coefficients
are normalized by a common shift, which changes no function.
"""
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


def family(n,k,core_step=Q(1)):
    H=tuple(range(-(k//2),k-(k//2)))
    core_H=tuple(int(core_step)*i if core_step.denominator==1 else core_step*i for i in range(k));keys=[]
    for s in range(1,n):
        for hc in histograms(s,k):
            if not hc[0]:continue
            for hl in histograms(n-1-s,k):keys.append((s,hc,hl))
    lookup={key:[] for key in keys}
    for a in range(n):
        other=[i for i in range(n) if i!=a]
        for s in range(1,n):
            for core in combinations(other,s):
                outside=[i for i in other if i not in core]
                for ch in product(core_H,repeat=s):
                    if min(ch)!=0:continue
                    hc=tuple(ch.count(v) for v in core_H)
                    for lh in product(H,repeat=len(outside)):
                        hl=tuple(lh.count(v) for v in H)
                        h=[0]*n
                        for i,v in zip(core,ch):h[i]=v
                        for i,v in zip(outside,lh):h[i]=v
                        lookup[s,hc,hl].append((a,core,tuple(h)))
    return H,keys,[lookup[key] for key in keys]


def atom_value(n,a,core,h,j,point):
    aa=point[a];den=1
    for i in range(n):
        if i in (a,j):continue
        q=point[i]-point[j]+aa*(h[i]-h[j]) if i in core else point[i]+aa*h[i]
        den*=q*(q+aa)
    return Q(len(core)*(-aa)**(n-4),den)


def values(n,columns,point):
    row=[]
    for column in columns:
        value=Q(0)
        for a,core,h in column:
            for j in core:value+=atom_value(n,a,core,h,j,point)
        row.append(value)
    row.append(Q((-1)**(n-1),math.prod(point)))
    return row


def expression(n,columns,cs,target):
    fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
    out=defaultdict(Q)
    for c,column in zip(cs,columns):
        if not c:continue
        for a,core,h in column:
            aa=fs[a]
            for j in core:
                den=[]
                for i in range(n):
                    if i in (a,j):continue
                    q=tuple(x-y+(h[i]-h[j])*z for x,y,z in zip(fs[i],fs[j],aa)) if i in core else tuple(x+h[i]*z for x,z in zip(fs[i],aa))
                    den.extend([(q,1),(tuple(x+z for x,z in zip(q,aa)),1)])
                add(out,c*len(core),tuple(-x for x in aa),n-4,den)
    if target:add(out,-((-1)**(n-1)),(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
    return out


def coordinate_value(n,unit,point):
    a,core,h=unit;s=len(core);idx=[i for i in range(n) if i!=a]
    mean=[Q(int(i in core),s) for i in range(n)]
    generators={j:[Q(int(i==j))-mean[i] for i in range(n)] for j in idx}
    head=[mean[i]-int(i==a)+sum(h[j]*generators[j][i] for j in idx) for i in range(n)]
    value=Q(0)
    for j in core:
        T=fmpq_mat([[str(v[i]) for i in idx] for v in [head]+[generators[t] for t in idx if t!=j]])
        det=abs(Q(str(T.det())));assert det==Q(1,s)
        dual=T.transpose().inv()*fmpq_mat([[point[i]] for i in idx])
        w=[Q(str(dual[i,0])) for i in range(n-1)];assert w[0]==-point[a]
        term=w[0]**(n-4)/det
        for z in w[1:]:term/=z*(z-w[0])
        assert term==atom_value(n,a,core,h,j,point)
        value+=term
    return value


def main(n,k,half_union=False):
    started=time.monotonic();H,keys,columns=family(n,k)
    keys=[(str(Q(1)),)+key for key in keys]
    if half_union:
        unused,extra_keys,extra_columns=family(n,k,Q(1,2));seen={tuple(column) for column in columns}
        for key,column in zip(extra_keys,extra_columns):
            if tuple(column) not in seen:
                seen.add(tuple(column));keys.append((str(Q(1,2)),)+key);columns.append(column)
    width=len(columns)
    print('FAMILY',n,k,'COLUMNS',width,'UNITS',sum(map(len,columns)),flush=True)
    rng=random.Random(24102485+31*n+k);points=[];rows=[];attempts=0
    # Reject all cut poles before any expensive exact orbit addition.
    while len(points)<width+10:
        p=[rng.randrange(1,1000) for _ in range(n-1)];p.append(-sum(p));attempts+=1
        try:row=values(n,columns,p)
        except ZeroDivisionError:continue
        points.append(p);rows.append(row)
        if len(rows)%10==0:print('ROWS',len(rows),'SECONDS',time.monotonic()-started,flush=True)
    rr,rank=fmpq_mat([[str(q) for q in r] for r in rows]).rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,head_values=H,core_head_values=list(range(k)),half_core_union=half_union,
              orbit_keys=keys,unit_count=sum(map(len,columns)),points=points,
              rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target),rank],
              producer_sha256=digest(Path(__file__)))
    print('EXACT RANKS',data['ranks'],'SECONDS',time.monotonic()-started,flush=True)
    independent=[sum((coordinate_value(n,u,points[0]) for u in col),Q(0)) for col in columns]
    assert independent==rows[0][:-1]
    data['independent_coordinate_full_rows']=1
    path=HERE/f'overnight_upper_circuit_{n}_h{k}{"_half_union" if half_union else ""}.json'
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            assert V.check(expression(n,columns,cs,False))
            vectors.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='EXACT_CIRCUIT_CORE_TOP_OBSTRUCTION',kernel_free_columns=free,
                    kernel_vectors=vectors,exact_kernel_count=len(vectors),ordinary_rank_upper=width-len(vectors))
    else:
        cs=[Q(0)]*width
        for i,j in enumerate(pivots):cs[j]=Q(str(rr[i,width]))
        data['coefficients']=list(map(str,cs));path.write_text(json.dumps(data,separators=(',',':'))+'\n')
        assert V.check(expression(n,columns,cs,True))
        data['status']='EXACT_TOP_IDENTITY'
    data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 3,len(sys.argv)>3 and sys.argv[3]=='half_union')
