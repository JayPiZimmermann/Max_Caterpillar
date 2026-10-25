#!/usr/bin/env python3
"""Exact interval DP for noncrossing-tree rooted-cut kernels.

The planted attachment state is essential: an external edge at v forbids
an internal edge straddling v. It factors into two endpoint-rooted states.
The resulting H recurrence is triangular, and specializes to H=1+z H^3
when every edge factor is1. Small independent Pruefer controls are included.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations,product
from pathlib import Path
import hashlib,json,math,random,sys,time
from flint import fmpq_mat

HERE=Path(__file__).parent


def interval_kernel(sequence,a,positive=1,negative=0):
    @lru_cache(None)
    def H(seq):
        if not seq:return Q(1)
        total=Q(0)
        for end in range(1,len(seq)+1):
            block=seq[:end];q=sum(block)
            edge=(Q(positive,q*(q+a)) if positive else Q(0))+(Q(negative,q*(q-a)) if negative else Q(0))
            planted=sum(H(block[:j])*H(block[j+1:]) for j in range(end))
            total+=edge*planted*H(seq[end:])
        return total
    return H(tuple(sequence))


def rooted_component(sequence,a,sign):
    return sum(interval_kernel(sequence[j+1:]+sequence[:j],a,int(sign==1),int(sign==-1))
               for j in range(len(sequence)))


def inward_columns(omega):
    n=len(omega);out=[]
    for p in range(1,n//2+1):
        total=Q(0)
        for shift in range(n):
            cyc=omega[shift:]+omega[:shift];left,right=cyc[:p],cyc[p:];a=sum(right)
            total+=Q(-a)**(n-4)*rooted_component(left,a,1)*rooted_component(right,a,-1)
        out.append(total)
    return out+[Q((-1)**(n-1),math.prod(omega))]


def pruefer(n):
    if n==1:yield ();return
    for code in product(range(n),repeat=n-2):
        degree=[1]*n;edges=[]
        for v in code:degree[v]+=1
        for v in code:
            leaf=next(i for i,d in enumerate(degree) if d==1);edges.append((leaf,v));degree[leaf]-=1;degree[v]-=1
        edges.append(tuple(i for i,d in enumerate(degree) if d==1));yield tuple(edges)


def crosses(e,f):
    a,b=sorted(e);c,d=sorted(f);return a<c<b<d or c<a<d<b


def brute_rooted(omega,a,root,positive,negative):
    n=len(omega);total=Q(0);count=0
    for edges in pruefer(n):
        if any(crosses(e,f) for e,f in combinations(edges,2)):continue
        count+=1;term=Q(1)
        for edge in edges:
            side={edge[0]};changed=True
            while changed:
                changed=False
                for e in edges:
                    if e==edge:continue
                    if bool(e[0] in side)!=bool(e[1] in side):side.update(e);changed=True
            if root in side:side=set(range(n))-side
            q=sum(omega[v] for v in side)
            term*=(Q(positive,q*(q+a)) if positive else Q(0))+(Q(negative,q*(q-a)) if negative else Q(0))
        total+=term
    return total,count


def controls():
    out=[]
    for n in range(2,6):
        omega=tuple(3**i for i in range(n));a=10000
        for root in range(n):
            for positive,negative in ((1,0),(0,1),(2,-3)):
                direct,count=brute_rooted(omega,a,root,positive,negative)
                got=interval_kernel(omega[root+1:]+omega[:root],a,positive,negative)
                assert direct==got,(n,root,positive,negative)
        out.append(dict(vertices=n,noncrossing_trees=count,checks=3*n))
    return out


def main():
    start=time.monotonic();checked=controls();records=[];rng=random.Random(251025)
    for n in range(3,10):
        rows=[];points=[]
        for j in range(n//2+8):
            pos=[rng.randrange(1,7)]
            while len(pos)<n-1:pos.append(sum(pos)+rng.randrange(1,7))
            omega=tuple([-sum(pos)]+pos);points.append(omega);rows.append(inward_columns(omega))
        integers=[]
        for row in rows:
            den=math.lcm(*(x.denominator for x in row));integers.append([int(x*den) for x in row])
        ordinary=fmpq_mat([r[:-1] for r in integers]).rank();augmented=fmpq_mat(integers).rank()
        record=dict(n=n,points=points,integer_rows=integers,ranks=[ordinary,augmented],columns=n//2)
        if ordinary==n//2 and augmented==ordinary+1:
            record['status']='EXACT_FULL_COLUMN_EVALUATION_EXCLUSION';records.append(record);print(record['status'],n,record['ranks'],flush=True);break
        record['status']='EVALUATION_DIAGNOSTIC'
        if ordinary==augmented:
            rr,rank=fmpq_mat(integers).rref();cs=['0']*(n//2)
            for i in range(rank):
                p=next(j for j in range(n//2) if rr[i,j]);cs[p]=str(rr[i,n//2])
            record['candidate_coefficients']=cs
        records.append(record);print(record['status'],n,record['ranks'],record.get('candidate_coefficients'),flush=True)
    result=dict(status='EXACT_INTERVAL_KERNEL_RECURRENCE_CONTROLS_AND_SCALAR_TARGET_TEST',controls=checked,records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
                scope='Tests weights depending only on component size, with all P edges positive away from its root and all Q edges negative away. No exclusion of arbitrary orientations or richer boundary states.')
    (HERE/'overnight_upper_interval_states.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
