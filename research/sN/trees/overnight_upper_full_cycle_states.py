#!/usr/bin/env python3
"""Enlarge the full-label circuit test by allowing any subset of its edges.

Heads have integer cyclic coefficient height <= B. The enumeration includes
all masks before dihedral quotienting, including shallow and full cycle
atoms. Formal states of a head-height-B0 full cycle lie inside B=B0+2.
"""
from itertools import product
from pathlib import Path
import hashlib,json,math,sys,time
import numpy as np
from flint import fmpq_mat,nmod_mat,ctx
import overnight_upper_full_cycle as base

HERE=Path(__file__).parent;P=1000000007;ctx.threads=1


def canonical(h,mask):
    n=len(h);out=[]
    reverse_mask=tuple(mask[-i-1] for i in range(n))
    reverse_head=tuple(-h[-i-1]-reverse_mask[i] for i in range(n))
    for head,edges in ((h,mask),(reverse_head,reverse_mask)):
        head=tuple(x-min(head) for x in head)
        for k in range(n):out.append((head[k:]+head[:k],edges[k:]+edges[:k]))
    return min(out)


def family(n,bound):
    return sorted({canonical(h,mask) for h in product(range(bound+1),repeat=n) if min(h)==0
                   for mask in product(range(2),repeat=n)})


def main(n,bound):
    started=time.monotonic();candidates=family(n,bound);heads,_=base.profiles(n);columns=[];keys=set()
    for h,mask in candidates:
        values=np.einsum('ijk,j->ik',heads,np.asarray(h,dtype=np.int16))
        values+=np.einsum('ijk,j->ik',np.maximum(heads,0),np.asarray(mask,dtype=np.int16))
        col=base.column(values);columns.append(col);keys.update(col[0])
    keys=sorted(keys);rows=[[c[0].get(k,0) for c in columns]+[0,0] for k in keys]
    for j in range(n-1):rows.append([c[1][j] for c in columns]+[(j+1)*(n-j-1),n-j-1])
    print('SYSTEM',n,bound,len(candidates),len(rows),'SECONDS',time.monotonic()-started,flush=True)
    rr,rank=nmod_mat(rows,P).rref();width=len(candidates)+1
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)]
    target=width in pivots;modranks=[rank-int(target),rank]
    print('MODULAR_RANKS',modranks,'SECONDS',time.monotonic()-started,flush=True)
    ordinary=fmpq_mat([r[:-1] for r in rows]).rank();augmented=fmpq_mat(rows).rank()
    record=dict(status='EXACT_CHAMBER_SPAN_INCLUSION' if ordinary==augmented else 'EXACT_CHAMBER_SPAN_EXCLUSION',
                n=n,head_height=bound,candidates=candidates,kink_normals=keys,integer_rows=rows,
                exact_ranks=[ordinary,augmented],modular_ranks=modranks,prime=P,
                scope='Full S_N sums of arbitrary subcycle atoms with integer cyclic-head height <= bound, plus pairwise-absolute-value auxiliary.',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                dependency_sha256=hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
    if ordinary==augmented:
        exact,rankq=fmpq_mat(rows).rref();coefficients=['0']*width
        for i in range(rankq):
            p=next(j for j in range(width) if exact[i,j]);coefficients[p]=str(exact[i,width])
        record['coefficients']=coefficients;record['nonzero_coefficients']=sum(c!='0' for c in coefficients)
    path=HERE/f'overnight_upper_full_cycle_states_n{n}_b{bound}.json'
    path.write_text(json.dumps(record,separators=(',',':'))+'\n')
    print('DONE',record['status'],'RANKS',record['exact_ranks'],'SECONDS',record['seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2]))
