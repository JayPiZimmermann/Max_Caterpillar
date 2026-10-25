#!/usr/bin/env python3
"""Keep the outward-orientation count in each NC interval component.

These are coefficient-state probes of the exact interval recurrence, not
head-alphabet searches. A sampled rank deficiency is not an exclusion.
Full augmented column rank is an exact finite obstruction to this ansatz.
"""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import hashlib,json,math,random,sys,time
from flint import fmpq_mat

HERE=Path(__file__).parent


def add(a,b):
    out=[Q(0)]*max(len(a),len(b))
    for i,v in enumerate(a):out[i]+=v
    for i,v in enumerate(b):out[i]+=v
    return out


def mul(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out


@lru_cache(None)
def H(seq,a):
    if not seq:return [Q(1)]
    total=[Q(0)]*(len(seq)+1)
    for end in range(1,len(seq)+1):
        block=seq[:end];q=sum(block);edge=[Q(1,q*(q-a)),Q(1,q*(q+a))]
        planted=[Q(0)]*end
        for j in range(end):planted=add(planted,mul(H(block[:j],a),H(block[j+1:],a)))
        total=add(total,mul(mul(edge,planted),H(seq[end:],a)))
    return total


def rooted(seq,a):
    total=[Q(0)]*len(seq)
    for j in range(len(seq)):total=add(total,H(seq[j+1:]+seq[:j],a))
    return total


def descriptors(n):
    out=[]
    for p in range(1,n//2+1):
        q=n-p
        for i in range(p):
            for j in range(q):
                if p==q and (i,j)>(p-1-j,p-1-i):continue
                out.append((p,i,j))
    return out


def row(omega):
    n=len(omega);columns={key:Q(0) for key in descriptors(n)}
    for p in range(1,n//2+1):
        for shift in range(n):
            cyc=omega[shift:]+omega[:shift];left,right=cyc[:p],cyc[p:];a=sum(right)
            f,g=rooted(left,a),rooted(right,a);pref=Q(-a)**(n-4)
            for key in columns:
                if key[0]==p:columns[key]+=pref*f[key[1]]*g[key[2]]
    H.cache_clear()
    return list(columns.values())+[Q((-1)**(n-1),math.prod(omega))]


def main(maximum):
    start=time.monotonic();rng=random.Random(251026);records=[]
    from overnight_upper_interval_states import brute_rooted
    controls=[]
    for n in range(2,6):
        omega=tuple(3**i for i in range(n));a=10000
        for root in range(n):
            coefficients=H(omega[root+1:]+omega[:root],a)
            for positive,negative in ((1,0),(0,1),(2,-3)):
                direct,count=brute_rooted(omega,a,root,positive,negative)
                value=sum(c*positive**i*negative**(n-1-i) for i,c in enumerate(coefficients))
                assert direct==value,(n,root,positive,negative)
        controls.append(dict(vertices=n,noncrossing_trees=count,checks=3*n))
    H.cache_clear()
    for n in range(3,maximum+1):
        desc=descriptors(n);rows=[];points=[]
        while len(rows)<len(desc)+6:
            pos=[rng.randrange(1,11)]
            while len(pos)<n-1:pos.append(3*sum(pos)+rng.randrange(1,11))
            omega=tuple([-sum(pos)]+pos)
            if omega in points:continue
            # Cyclic/reversal symmetry is retained, but no full S_N averaging.
            try:values=row(omega)
            except ZeroDivisionError:H.cache_clear();continue
            den=math.lcm(*(v.denominator for v in values));rows.append([int(v*den) for v in values]);points.append(omega)
        ordinary=fmpq_mat([r[:-1] for r in rows]).rank();augmented=fmpq_mat(rows).rank()
        rec=dict(n=n,descriptors=desc,points=points,integer_rows=rows,ranks=[ordinary,augmented])
        rec['status']='EXACT_FULL_COLUMN_OBSTRUCTION' if ordinary==len(desc) and augmented==ordinary+1 else 'EVALUATION_DIAGNOSTIC'
        if ordinary==augmented:
            rr,rank=fmpq_mat(rows).rref();cs=['0']*len(desc)
            for i in range(rank):
                p=next(j for j in range(len(desc)) if rr[i,j]);cs[p]=str(rr[i,len(desc)])
            rec['candidate_coefficients']=cs
        records.append(rec);print('N',n,'COLS',len(desc),'RANKS',rec['ranks'],rec['status'],'SECONDS',time.monotonic()-start,flush=True)
        if augmented>ordinary:break
    out=dict(status='ORIENTATION_COUNT_BOUNDARY_STATE_PROBE',controls=controls,records=records,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
             scope='Coefficients depend only on component size and the numbers of positive-away edges in each component; root positions and tree shapes are summed uniformly.')
    (HERE/'overnight_upper_interval_polynomial.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main(int(sys.argv[1]) if len(sys.argv)>1 else 8)
