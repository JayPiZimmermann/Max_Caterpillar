#!/usr/bin/env python3
"""Preserve a modular particular solution and try asymmetric reconstruction."""
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import sys
import time

from flint import nmod_mat
import overnight_upper_block as B

HERE=Path(__file__).parent


def reconstruct(value,prime,numerator_bound):
    if not value:return Q(0)
    r0,r1,t0,t1=prime,int(value),0,1
    while abs(r1)>numerator_bound:
        q=r0//r1;r0,r1,t0,t1=r1,r0-q*r1,t1,t0-q*t1
    denominator_bound=(prime-1)//(2*numerator_bound)
    if not t1 or abs(t1)>denominator_bound:return None
    q=Q(r1,t1)
    return q if (q.numerator-value*q.denominator)%prime==0 else None


def extract(mode):
    started=time.monotonic();stem,meta,dp,sp=B.paths(mode);data=json.loads(meta.read_text())
    assert data['status']=='SCHUR_COMPLETE' and B.base.digest(sp)==data['schur_sha256']
    r,c=data['prefix_rows'],data['schur_cols'];q=data['remaining'];p=data['pivots']
    matrix=B.read_matrix(sp,data['schur_rows'],c)
    print('SCHUR LOADED',time.monotonic()-started,flush=True)
    reduced,rank=matrix.rref(inplace=True)
    pivots=[next(j for j in range(c) if reduced[i,j]) for i in range(rank)]
    assert c-1 not in pivots
    z=nmod_mat(c,1,B.P);z[c-1,0]=1
    for i,j in enumerate(pivots):z[j,0]=-reduced[i,c-1]
    del matrix,reduced
    D=B.read_matrix(dp,r,c);v=-(D*z);del D
    coeff=[0]*(data['cols']-1)
    for i,j in enumerate(q):
        if j<len(coeff):coeff[j]=(-int(z[i,0]))%B.P
    for i,j in enumerate(p):coeff[j]=(-int(v[i,0]))%B.P
    out=dict(status='MODULAR_SOLUTION_ONLY',mode=mode,prime=B.P,coefficients_mod_prime=coeff,
             pivot_columns=p+[q[j] for j in pivots],ranks=[r+rank,r+rank],
             source_block_sha256=B.base.digest(meta),matrix_sha256=data['original_matrix_sha256'],
             producer_sha256=B.base.digest(Path(__file__)),elapsed_seconds=time.monotonic()-started)
    path=HERE/f'overnight_upper_{mode}_solution.json';path.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('EXTRACTED','SUPPORT',sum(bool(x) for x in coeff),'SECONDS',out['elapsed_seconds'],flush=True)


def recover(mode):
    path=HERE/f'overnight_upper_{mode}_solution.json';data=json.loads(path.read_text());p=data['prime'];values=data['coefficients_mod_prime']
    attempts=[];proposals=[]
    bounds=[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,math.isqrt(p//2),32768,65536,131072,262144,524288,1048576]
    for bound in bounds:
        if 2*bound>=p:continue
        cs=[reconstruct(x,p,bound) for x in values];count=sum(c is not None for c in cs)
        record=dict(numerator_bound=bound,denominator_bound=(p-1)//(2*bound),reconstructed=count,total=len(cs))
        if count==len(cs):
            denominator=math.lcm(*(c.denominator for c in cs))
            record.update(common_denominator_bits=denominator.bit_length(),max_numerator=max(abs(c.numerator) for c in cs))
            if denominator.bit_length()<256:record['common_denominator']=denominator
            proposals.append(dict(**record,coefficients=list(map(str,cs))))
        attempts.append(record);print(json.dumps(record),flush=True)
    data['reconstruction_attempts']=attempts;data['rational_proposals']=proposals
    data['status']='RATIONAL_PROPOSALS_PENDING_EXACT_GATE' if proposals else 'MODULAR_SOLUTION_NO_BOUNDED_RECONSTRUCTION'
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')


if __name__=='__main__':globals()[sys.argv[2]](sys.argv[1])
