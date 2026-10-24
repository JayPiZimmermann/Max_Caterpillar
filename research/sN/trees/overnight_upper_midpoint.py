#!/usr/bin/env python3
"""Midpoint-centre star atoms: exact symmetric finite test outside tree model."""
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
H=(-2,-1,0,1)
D=(Q(0),Q(1,2),Q(1))
LABEL=''


def values(point,hist):
    n=len(point);out={(d,h):Q(0) for d in D for h in hist};zero=(0,)*len(H)
    for a in range(n):
        aa=point[a]
        for c in range(n):
            if c==a:continue
            for d in range(n):
                if d in (a,c):continue
                q=Q(point[c]-point[d],2)
                cores={delta:Q(1,(q+aa*(delta-Q(1,2)))*(q+aa*(delta+Q(1,2)))) for delta in D}
                dp={zero:Q(1)}
                for i,w in enumerate(point):
                    if i in (a,c,d):continue
                    factors=[Q(1,(w+h*aa)*(w+(h+1)*aa)) for h in H]
                    nxt=defaultdict(Q)
                    for counts,v in dp.items():
                        for j,f in enumerate(factors):
                            hh=list(counts);hh[j]+=1;nxt[tuple(hh)]+=v*f
                    dp=nxt
                for delta,core in cores.items():
                    for hh,v in dp.items():out[delta,hh]+=(-aa)**(n-4)*core*v
    return [out[delta,hh] for delta in D for hh in hist]+[Q((-1)**(n-1),math.prod(point))]


def units(n,hist):
    out={(delta,h):[] for delta in D for h in hist}
    for a in range(n):
        for c in range(n):
            if c==a:continue
            for d in range(n):
                if d in (a,c):continue
                leaves=[i for i in range(n) if i not in (a,c,d)]
                for digits in product(range(len(H)),repeat=n-3):
                    hh=tuple(digits.count(j) for j in range(len(H)))
                    for delta in D:out[delta,hh].append((a,c,d,delta,tuple(zip(leaves,[H[j] for j in digits]))))
    return [out[delta,hh] for delta in D for hh in hist]


def affine_forms(n,unit):
    a,c,d,delta,leaves=unit
    fs=[tuple(Q(int(i==j)) for i in range(n-1))+(Q(0),) for j in range(n-1)]+[(Q(-1),)*(n-1)+(Q(0),)]
    core=tuple((x-y)/2 for x,y in zip(fs[c],fs[d]));aa=fs[a]
    den=[(tuple(x+(delta+s)*y for x,y in zip(core,aa)),1) for s in (Q(-1,2),Q(1,2))]
    den.extend((tuple(x+(h+s)*y for x,y in zip(fs[i],aa)),1) for i,h in leaves for s in (0,1))
    return fs,aa,den


def expression(n,columns,coefficients,target):
    out=defaultdict(Q)
    for column,coeff in zip(columns,coefficients):
        if not coeff:continue
        for unit in column:
            fs,aa,den=affine_forms(n,unit)
            add(out,coeff,tuple(-x for x in aa),n-4,den)
    if target:
        fs,aa,den=affine_forms(n,columns[0][0])
        add(out,-((-1)**(n-1)),(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
    return out


def coordinate_control(unit,point):
    """Independent determinant/dual-coordinate calculation for a full atom."""
    n=len(point);a,c,d,delta,leaves=unit;idx=[i for i in range(n) if i!=a]
    m=[Q(int(i in (c,d)),2) for i in range(n)]
    g0=[Q(int(i==c)-int(i==d)) for i in range(n)]
    gs=[g0]+[[Q(int(i==j))-m[i] for i in range(n)] for j,h in leaves]
    head=[m[i]-int(i==a)+(delta-Q(1,2))*g0[i]+sum(h*g[i] for (j,h),g in zip(leaves,gs[1:])) for i in range(n)]
    T=fmpq_mat([[str(v[i]) for i in idx] for v in [head]+gs])
    dual=T.transpose().inv()*fmpq_mat([[point[i]] for i in idx])
    freq=[Q(str(dual[i,0])) for i in range(n-1)]
    det=abs(Q(str(T.det())));assert det==1 and freq[0]==-point[a]
    result=freq[0]**(n-4)/det
    for z in freq[1:]:result/=z*(z-freq[0])
    fs,aa,den=affine_forms(n,unit)
    direct=Q((-point[a])**(n-4))
    for f,p in den:direct/=sum(x*y for x,y in zip(f[:-1],point[:-1]))**p
    assert result==direct
    return result


def main(n):
    started=time.monotonic();hist=histograms(n-3,len(H));width=len(D)*len(hist)
    rng=random.Random(24102481+n);points=[];rows=[]
    while len(points)<width+10:
        p=[rng.randrange(1,90) for _ in range(n-1)];p.append(-sum(p))
        try:row=values(p,hist)
        except ZeroDivisionError:continue
        points.append(p);rows.append(row)
    matrix=fmpq_mat([[str(q) for q in row] for row in rows]);rr,rank=matrix.rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,head_values=list(map(str,H)),core_parameters=list(map(str,D)),
              histograms=hist,points=points,rational_rows=[[str(q) for q in r] for r in rows],
              ranks=[rank-int(target),rank],producer_sha256=digest(Path(__file__)))
    print('EXACT RANKS',data['ranks'],'COLS',width,'SECONDS',time.monotonic()-started,flush=True)
    columns=units(n,hist)
    for column in columns:coordinate_control(column[0],points[0])
    for row,p in zip(rows[:2],points[:2]):
        assert [sum((coordinate_control(u,p) for u in col),Q(0)) for col in columns]==row[:-1]
    data.update(independent_coordinate_full_rows=2,coordinate_controls=sum(map(len,columns))*2+len(columns))
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            assert V.check(expression(n,columns,cs,False))
            vectors.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='EXACT_MIDPOINT_STAR_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=vectors,
                    exact_kernel_count=len(vectors),ordinary_rank_upper=width-len(vectors))
    else:
        cs=[Q(0)]*width
        for i,j in enumerate(pivots):cs[j]=Q(str(rr[i,width]))
        ok=V.check(expression(n,columns,cs,True))
        data.update(status='EXACT_TOP_IDENTITY' if ok else 'PROPOSAL_FAILED',coefficients=list(map(str,cs)))
    data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
    (HERE/f'overnight_upper_midpoint_{LABEL}{n}.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':
    if len(sys.argv)>2 and sys.argv[2]=='reciprocal':
        H=(-2,-1,Q(-1,2),0,1);LABEL='reciprocal_'
    main(int(sys.argv[1]))
