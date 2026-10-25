#!/usr/bin/env python3
"""Uniform exponential candidate via a one-hidden-layer tropical restriction.

L_i=x_i+sum_j sigma(x_j-x_i) has min(L)=max(x), and its image is exactly
the set where the minimum is attained at least twice. Test whether min(L)
on that set has an S_N-symmetric shallow extension with coefficient alphabet
[-B,B]. A successful all-N fixed-B identity would give an exponential
two-hidden-layer construction. Histograms reduce the finite tests to small
exact kink/value systems; no ordering of N! coordinates is enumerated.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib,json,math,sys,time
from flint import fmpq_mat,nmod_mat

HERE=Path(__file__).parent
P=1000000007


def compositions(n,k):
    if k==1:yield (n,);return
    for first in range(n+1):
        for rest in compositions(n-first,k-1):yield (first,)+rest


def system(n,bound):
    alphabet=tuple(range(-bound,bound+1));width=len(alphabet)
    candidates=[k for k in compositions(n,width) if sum(a*c for a,c in zip(alphabet,k))==0 and k[bound]!=n]
    remove=list(compositions(2,width));columns=[];keys=set()
    for k in candidates:
        kinks=defaultdict(int);value=0
        for delta in remove:
            if any(d>c for d,c in zip(delta,k)):continue
            rho=tuple(c-d for c,d in zip(k,delta));multiplicity=2//math.prod(math.factorial(d) for d in delta)
            remaining=tuple(a for a,c in zip(alphabet,rho) for _ in range(c))
            count=math.factorial(n-2)//math.prod(math.factorial(c) for c in rho)
            value+=multiplicity*count*max(sum(remaining),0)
            if min(remaining)<0<max(remaining):
                g=math.gcd(*remaining);primitive=tuple(a//g for a in remaining)
                key=min(primitive,tuple(sorted(-a for a in primitive)))
                kinks[key]+=g*multiplicity;keys.add(key)
        columns.append((dict(kinks),value))
    keys=sorted(keys);rows=[[col[0].get(key,0) for col in columns]+[0] for key in keys]
    rows.append([col[1] for col in columns]+[-(n-2)])
    return alphabet,candidates,keys,rows


def control(n,bound):
    alphabet,candidates,keys,rows=system(n,bound);direct=[]
    for counts in candidates:
        vector=tuple(a for a,c in zip(alphabet,counts) for _ in range(c));kinks=defaultdict(int);value=0
        for perm in set(permutations(vector)):
            remaining=perm[2:];value+=max(sum(remaining),0)
            if min(remaining)<0<max(remaining):
                g=math.gcd(*remaining);primitive=tuple(sorted(a//g for a in remaining));key=min(primitive,tuple(sorted(-a for a in primitive)))
                kinks[key]+=g
        direct.append((kinks,value))
    # The histogram row represents one concrete hyperplane, whereas this
    # permutation control sums all hyperplanes in its permutation orbit.
    for row,key in zip(rows[:-1],keys):
        orbit=math.factorial(n-2)//math.prod(math.factorial(key.count(v)) for v in set(key))
        assert [x*orbit for x in row[:-1]]==[col[0].get(key,0) for col in direct]
    assert rows[-1][:-1]==[c[1] for c in direct]


def main(bound,maximum):
    started=time.monotonic();control(4,bound);results=[]
    for n in range(3,maximum+1):
        alphabet,candidates,keys,rows=system(n,bound)
        ordinary=fmpq_mat([r[:-1] for r in rows]).rank();augmented=fmpq_mat(rows).rank()
        record=dict(n=n,columns=len(candidates),constraints=len(rows),exact_ranks=[ordinary,augmented])
        results.append(record);print(record,flush=True)
        if augmented>ordinary:
            out=dict(status='EXACT_TROPICAL_RESTRICTION_OBSTRUCTION',alphabet=alphabet,n=n,candidate_histograms=candidates,
                     kink_histograms=keys,integer_rows=rows,results=results,
                     producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
            (HERE/f'overnight_upper_tropical_min_b{bound}.json').write_text(json.dumps(out,separators=(',',':'))+'\n');break
    else:
        out=dict(status='FINITE_TROPICAL_RESTRICTION_INCLUSIONS_NOT_UNIFORM_PROOF',alphabet=alphabet,results=results,
                 producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
        (HERE/f'overnight_upper_tropical_min_b{bound}.json').write_text(json.dumps(out,separators=(',',':'))+'\n')


if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2]))
