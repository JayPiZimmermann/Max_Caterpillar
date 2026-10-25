#!/usr/bin/env python3
"""Exact full-S_N chamber control for full-label circuit pyramids.

Atoms are sigma(sum h_i (x_i-x_(i+1)) + sum_i sigma(x_i-x_(i+1))).
The integer head h is considered modulo a common shift; max(h)-min(h)<=B.
All cycle orders are allowed through full permutation sums. This is a
necessary control, not an exponential bound on the number of cycle orders.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations,product
from pathlib import Path
import hashlib,json,math,sys,time
import numpy as np
from flint import fmpq_mat,nmod_mat,ctx

HERE=Path(__file__).parent
P=1000000007
ctx.threads=1


def canonical(h):
    n=len(h);out=[]
    for v in (h,tuple(-h[-i-1] for i in range(n))):
        v=tuple(x-min(v) for x in v)
        out.extend(v[k:]+v[:k] for k in range(n))
    return min(out)


def family(n,bound):
    return sorted({canonical(h) for h in product(range(bound+1),repeat=n) if min(h)==0})


def profiles(n):
    heads=[];hinges=[]
    for pi in permutations(range(n)):
        position={v:i for i,v in enumerate(pi)};forms=[]
        for i in range(n):
            j=(i+1)%n
            forms.append([int(position[i]<=k)-int(position[j]<=k) for k in range(n-1)])
        heads.append(forms)
        hinges.append([sum(max(form[k],0) for form in forms) for k in range(n-1)])
    return np.asarray(heads,dtype=np.int16),np.asarray(hinges,dtype=np.int16)


def column(values):
    kinks=defaultdict(int);linear=[0]*values.shape[1]
    for raw in values:
        a=tuple(map(int,raw))
        if min(a)>=0:
            linear=[x+y for x,y in zip(linear,a)];continue
        if max(a)<=0:continue
        divisor=math.gcd(*a);sign=1 if next(x for x in a if x)>0 else -1
        key=tuple(x//(sign*divisor) for x in a);kinks[key]+=divisor
        if sign<0:linear=[x+y for x,y in zip(linear,a)]
    return dict(kinks),linear


def control(n,candidates,heads,hinges):
    gaps=np.arange(1,n,dtype=np.int64);x=np.asarray([sum(gaps[i:]) for i in range(n)],dtype=np.int64)
    for h in candidates[::max(1,len(candidates)//11)]:
        direct=0
        for pi in permutations(range(n)):
            y=x[list(pi)];g=[int(y[i]-y[(i+1)%n]) for i in range(n)]
            direct+=max(sum(a*b for a,b in zip(h,g))+sum(max(v,0) for v in g),0)
        values=np.einsum('ijk,j->ik',heads,np.asarray(h,dtype=np.int16))+hinges
        assert direct==sum(max(int(v@gaps),0) for v in values)
        # Dihedral head normalization represents the same orbit sum.
        reflected=tuple(-h[-i-1] for i in range(n));reflected=tuple(z-min(reflected) for z in reflected)
        other=np.einsum('ijk,j->ik',heads,np.asarray(reflected,dtype=np.int16))+hinges
        assert column(values)==column(other)


def main(n,bound):
    started=time.monotonic();candidates=family(n,bound);heads,hinges=profiles(n)
    control(n,candidates,heads,hinges);columns=[];keys=set()
    for i,h in enumerate(candidates):
        col=column(np.einsum('ijk,j->ik',heads,np.asarray(h,dtype=np.int16))+hinges)
        columns.append(col);keys.update(col[0])
    keys=sorted(keys);rows=[[c[0].get(k,0) for c in columns]+[0,0] for k in keys]
    for j in range(n-1):rows.append([c[1][j] for c in columns]+[(j+1)*(n-j-1),n-j-1])
    print('SYSTEM',n,bound,len(candidates),len(rows),'SECONDS',time.monotonic()-started,flush=True)
    rr,rank=nmod_mat(rows,P).rref();width=len(candidates)+1
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)]
    target=width in pivots;modranks=[rank-int(target),rank]
    ordinary=fmpq_mat([r[:-1] for r in rows]).rank();augmented=fmpq_mat(rows).rank()
    record=dict(status='EXACT_CHAMBER_SPAN_INCLUSION' if ordinary==augmented else 'EXACT_CHAMBER_SPAN_EXCLUSION',
                n=n,head_height=bound,candidates=candidates,kink_normals=keys,integer_rows=rows,
                exact_ranks=[ordinary,augmented],modular_ranks=modranks,prime=P,
                scope='Full S_N sums of full-label cycle atoms with integer head height <= bound, plus pairwise-absolute-value auxiliary. Formal face states are not included.',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
    if ordinary==augmented:
        exact,rankq=fmpq_mat(rows).rref();coefficients=[Q(0)]*width
        for i in range(rankq):
            p=next(j for j in range(width) if exact[i,j]);coefficients[p]=Q(str(exact[i,width]))
        assert all(sum(c*x for c,x in zip(coefficients,row[:-1]))==row[-1] for row in rows)
        record['coefficients']=list(map(str,coefficients))
        record['nonzero_coefficients']=sum(bool(c) for c in coefficients)
    path=HERE/f'overnight_upper_full_cycle_n{n}_b{bound}.json'
    path.write_text(json.dumps(record,separators=(',',':'))+'\n')
    print('DONE',record['status'],'RANKS',record['exact_ranks'],'SECONDS',record['seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2]))
