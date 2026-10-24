#!/usr/bin/env python3
"""Integer general heads and apex scales1,2: exact weighted-star reopening."""
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
from rational_identity import Verifier,add
from overnight_upper_probe import digest

HERE=Path(__file__).parent
H=(-3,-2,-1,0,1,2)
C=(1,2)


def values(point,hist):
    n=len(point);out={(c,h):Q(0) for c in C for h in hist};zero=(0,)*len(H)
    for c in C:
        for apex,a in enumerate(point):
            for centre in range(n):
                if centre==apex:continue
                dp={zero:Q(1)}
                for i,w in enumerate(point):
                    if i in (apex,centre):continue
                    factors=[Q(1,(c*w+a*h)*(c*w+a*(h+1))) for h in H]
                    nxt=defaultdict(Q)
                    for counts,v in dp.items():
                        for j,f in enumerate(factors):
                            t=list(counts);t[j]+=1;nxt[tuple(t)]+=v*f
                    dp=nxt
                for hh,v in dp.items():out[c,hh]+=c**(n-1)*(-a)**(n-4)*v
    return [out[c,hh] for c in C for hh in hist]+[Q((-1)**(n-1),math.prod(point))]


def family(n,hist):
    out={(c,h):[] for c in C for h in hist}
    for c in C:
        for a in range(n):
            for b in range(n):
                if a==b:continue
                leaves=[i for i in range(n) if i not in (a,b)]
                for heads in product(H,repeat=n-2):
                    hh=tuple(heads.count(v) for v in H)
                    out[c,hh].append((c,a,b,tuple(zip(leaves,heads))))
    return [out[c,h] for c in C for h in hist]


def expression(n,columns,cs,target):
    fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
    out=defaultdict(Q)
    for coeff,column in zip(cs,columns):
        if not coeff:continue
        for c,a,b,heads in column:
            den=[]
            for i,h in heads:
                den.extend((tuple(c*x+(h+s)*y for x,y in zip(fs[i],fs[a])),1) for s in (0,1))
            add(out,coeff*c**(n-1),tuple(-x for x in fs[a]),n-4,den)
    if target:add(out,-((-1)**(n-1)),(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
    return out


def coordinate_value(unit,point):
    n=len(point);c,a,b,heads=unit;idx=[i for i in range(n) if i!=a]
    h=[0]*n;h[a]=-c;h[b]=c-sum(v for i,v in heads)
    for i,v in heads:h[i]=v
    generators=[[int(i==j)-int(i==b) for i in range(n)] for j,v in heads]
    T=fmpq_mat([[v[i] for i in idx] for v in [h]+generators]);assert abs(T.det())==c
    w=T.transpose().inv()*fmpq_mat([[point[i]] for i in idx]);dual=[Q(str(w[i,0])) for i in range(n-1)]
    assert dual[0]==Q(-point[a],c)
    value=dual[0]**(n-4)/c
    for z in dual[1:]:value/=z*(z-dual[0])
    return value


def main(n):
    started=time.monotonic();hist=histograms(n-2,len(H));width=len(C)*len(hist)
    rng=random.Random(24102491+n);rows=[];points=[]
    while len(rows)<width+10:
        p=[rng.randrange(1,300) for _ in range(n-1)];p.append(-sum(p))
        try:row=values(p,hist)
        except ZeroDivisionError:continue
        rows.append(row);points.append(p)
    rr,rank=fmpq_mat([[str(q) for q in r] for r in rows]).rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,head_values=H,apex_scales=C,histograms=hist,
              points=points,rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target),rank],
              producer_sha256=digest(Path(__file__)))
    print('EXACT RANKS',data['ranks'],'COLS',width,'SECONDS',time.monotonic()-started,flush=True)
    columns=family(n,hist)
    assert [sum((coordinate_value(u,points[0]) for u in col),Q(0)) for col in columns]==rows[0][:-1]
    data['independent_coordinate_full_rows']=1
    path=HERE/f'overnight_upper_weighted_star_{n}.json';path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            assert V.check(expression(n,columns,cs,False))
            vectors.append([[j,str(v)] for j,v in enumerate(cs) if v])
        data.update(status='EXACT_WEIGHTED_STAR_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=vectors,
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
