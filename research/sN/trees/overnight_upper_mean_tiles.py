#!/usr/bin/env python3
"""Individual positive-circuit tiles, with a marked omitted core generator.

Each nonapex/noncentre label chooses a core or leaf role and one head value.
This is an exponential independent-generator family, distinct from summing all
tiles of a circuit with a common coefficient.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
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
HEADS=(-1,0,1)
TYPES=tuple((core,h) for core in (False,True) for h in HEADS)
LABEL=''


def values(p,hist):
    n=len(p);zero=(0,)*len(TYPES);out={h:Q(0) for h in hist}
    for a in range(n):
        for j in range(n):
            if j==a:continue
            dp={zero:Q(1)}
            for i in range(n):
                if i in (a,j):continue
                factors=[]
                for core,h in TYPES:
                    q=p[i]-(p[j] if core else 0)+p[a]*h
                    factors.append(Q(1,q*(q+p[a])))
                nxt=defaultdict(Q)
                for counts,c in dp.items():
                    for t,f in enumerate(factors):
                        hh=list(counts);hh[t]+=1;nxt[tuple(hh)]+=c*f
                dp=nxt
            for hh,c in dp.items():
                s=1+sum(count for count,(core,h) in zip(hh,TYPES) if core)
                out[hh]+=s*(-p[a])**(n-4)*c
    return [out[h] for h in hist]+[Q((-1)**(n-1),math.prod(p))]


def family(n,hist):
    out={h:[] for h in hist}
    for a in range(n):
        for j in range(n):
            if j==a:continue
            other=[i for i in range(n) if i not in (a,j)]
            for digits in product(range(len(TYPES)),repeat=n-2):
                hh=tuple(digits.count(k) for k in range(len(TYPES)))
                out[hh].append((a,j,tuple((i,)+TYPES[d] for i,d in zip(other,digits))))
    return [out[h] for h in hist]


def expression(n,columns,cs,target):
    fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
    out=defaultdict(Q)
    for coeff,col in zip(cs,columns):
        if not coeff:continue
        for a,j,assign in col:
            den=[];s=1+sum(core for i,core,h in assign)
            for i,core,h in assign:
                q=tuple(x-(y if core else 0)+h*z for x,y,z in zip(fs[i],fs[j],fs[a]))
                den.extend([(q,1),(tuple(x+z for x,z in zip(q,fs[a])),1)])
            add(out,coeff*s,tuple(-x for x in fs[a]),n-4,den)
    if target:add(out,-((-1)**(n-1)),(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
    return out


def coordinate_value(n,unit,p):
    a,j,assign=unit;core={j}|{i for i,c,h in assign if c};idx=[i for i in range(n) if i!=a]
    mean=[Q(int(i in core),len(core)) for i in range(n)]
    generators=[[Q(int(i==v))-mean[i] for i in range(n)] for v,c,h in assign]
    head=[mean[i]-int(i==a)+sum(h*g[i] for (v,c,h),g in zip(assign,generators)) for i in range(n)]
    T=fmpq_mat([[str(v[i]) for i in idx] for v in [head]+generators]);det=abs(Q(str(T.det())))
    assert det==Q(1,len(core));cov=T.transpose().inv()*fmpq_mat([[p[i]] for i in idx])
    w=[Q(str(cov[i,0])) for i in range(n-1)];assert w[0]==-p[a]
    value=w[0]**(n-4)/det
    for z in w[1:]:value/=z*(z-w[0])
    return value


def main(n):
    started=time.monotonic();hist=histograms(n-2,len(TYPES));width=len(hist)
    rng=random.Random(24102501+n);points=[];rows=[]
    while len(rows)<width+10:
        p=[rng.randrange(1,1000) for _ in range(n-1)];p.append(-sum(p))
        try:row=values(p,hist)
        except ZeroDivisionError:continue
        rows.append(row);points.append(p)
    rr,rank=fmpq_mat([[str(q) for q in r] for r in rows]).rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,types=TYPES,histograms=hist,points=points,
              rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target),rank],
              producer_sha256=digest(Path(__file__)))
    print('EXACT RANKS',data['ranks'],'COLS',width,'SECONDS',time.monotonic()-started,flush=True)
    columns=family(n,hist)
    assert [sum((coordinate_value(n,u,points[0]) for u in col),Q(0)) for col in columns]==rows[0][:-1]
    data['independent_coordinate_full_rows']=1
    path=HERE/f'overnight_upper_mean_tiles_{LABEL}{n}.json';path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            vectors.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='RATIONAL_KERNEL_PROPOSALS_PENDING_EXACT_GATE',kernel_free_columns=free,kernel_vectors=vectors,exact_kernel_passed=[])
        path.write_text(json.dumps(data,separators=(',',':'))+'\n')
        for index,vector in enumerate(vectors):
            cs=[Q(0)]*width
            for j,c in vector:cs[j]=Q(c)
            try:ok=V.check(expression(n,columns,cs,False))
            except TimeoutError:
                data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
                path.write_text(json.dumps(data,separators=(',',':'))+'\n')
                print('PARTIAL EXACT',len(data['exact_kernel_passed']),'/',len(vectors),flush=True);return
            assert ok;data['exact_kernel_passed'].append(index)
            if (index+1)%10==0:
                path.write_text(json.dumps(data,separators=(',',':'))+'\n');print('EXACT',index+1,'/',len(vectors),flush=True)
        data.update(status='EXACT_MEAN_TILE_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=vectors,
                    exact_kernel_count=len(vectors),ordinary_rank_upper=width-len(vectors))
    else:
        cs=[Q(0)]*width
        for i,j in enumerate(pivots):cs[j]=Q(str(rr[i,width]))
        data['coefficients']=list(map(str,cs));path.write_text(json.dumps(data,separators=(',',':'))+'\n')
        assert V.check(expression(n,columns,cs,True));data['status']='EXACT_TOP_IDENTITY'
    data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':
    if len(sys.argv)>2 and sys.argv[2]=='wide':
        TYPES=tuple((False,h) for h in range(-2,2))+tuple((True,h) for h in range(-4,4));LABEL='wide_'
    main(int(sys.argv[1]))
