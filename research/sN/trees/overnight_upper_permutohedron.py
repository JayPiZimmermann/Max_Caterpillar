#!/usr/bin/env python3
"""Exact symmetric subset-permutohedron control, no factorial permutation sum.

Atoms are sigma(delta*(mean_S(x)-x_a)+lambda*sum_(i<j in S)|xi-xj|),
with a outside S, delta=+-1, and finitely many nonnegative rational lambda.
One column sums distinct (a,S) of a fixed size; subsets supply all lower
arities but are not claimed to contain all permutohedron face functions.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,math,sys,time
from flint import fmpq_mat,ctx

HERE=Path(__file__).parent;ctx.threads=1


def column(n,size,delta,lam):
    kinks=defaultdict(Q);linear=[Q(0)]*(n-1)
    for apex in range(n):
        for subset in combinations([i for i in range(n) if i!=apex],size):
            coeff=[Q(0)]*n;coeff[apex]=-delta
            for rank,i in enumerate(subset):coeff[i]=Q(delta,size)+lam*(size-2*rank-1)
            gaps=tuple(sum(coeff[:j+1]) for j in range(n-1))
            if min(gaps)>=0:
                linear=[x+y for x,y in zip(linear,gaps)];continue
            if max(gaps)<=0:continue
            den=math.lcm(*(x.denominator for x in gaps));integers=tuple(int(x*den) for x in gaps)
            divisor=math.gcd(*integers);sign=1 if next(x for x in integers if x)>0 else -1
            key=tuple(x//(sign*divisor) for x in integers);kinks[key]+=Q(divisor,den)
            if sign<0:linear=[x+y for x,y in zip(linear,gaps)]
    return dict(kinks),linear


def main(n,height):
    start=time.monotonic();lambdas=sorted({Q(p,q) for p in range(height+1) for q in range(1,height+1)})
    candidates=[(s,d,l) for s in range(2,n) for d in (-1,1) for l in lambdas]
    columns=[column(n,*args) for args in candidates];keys=sorted({key for c in columns for key in c[0]})
    rows=[[c[0].get(k,Q(0)) for c in columns]+[Q(0),Q(0)] for k in keys]
    for j in range(n-1):rows.append([c[1][j] for c in columns]+[Q((j+1)*(n-j-1)),Q(n-j-1)])
    integers=[]
    for row in rows:
        den=math.lcm(*(x.denominator for x in row));integers.append([int(x*den) for x in row])
    ordinary=fmpq_mat([r[:-1] for r in integers]).rank();augmented=fmpq_mat(integers).rank()
    record=dict(status='EXACT_PERMUTOHEDRAL_SUBSET_INCLUSION' if ordinary==augmented else 'EXACT_PERMUTOHEDRAL_SUBSET_EXCLUSION',
                n=n,rational_height=height,candidates=[(s,d,str(l)) for s,d,l in candidates],kinks=keys,
                integer_rows=integers,exact_ranks=[ordinary,augmented],columns=len(candidates),constraints=len(rows),
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
                scope='Symmetric mean heads, a single uniform edge weight per clique, listed finite lambda alphabet, all label subsets; no general heads or whole face closure claim.')
    if ordinary==augmented:
        rr,rank=fmpq_mat(integers).rref();coeff=['0']*(len(candidates)+1)
        for i in range(rank):
            p=next(j for j in range(len(coeff)) if rr[i,j]);coeff[p]=str(rr[i,len(coeff)])
        record['coefficients']=coeff
        record['selected']=[(c,str(a)) for c,a in zip(record['candidates'],coeff) if a!='0']
    (HERE/f'overnight_upper_permutohedron_n{n}_h{height}.json').write_text(json.dumps(record,separators=(',',':'))+'\n')
    print(record['status'],n,height,'RANKS',record['exact_ranks'],'COLS',len(candidates),'ROWS',len(rows),'SECONDS',record['seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2]))
