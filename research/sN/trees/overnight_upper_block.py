#!/usr/bin/env python3
"""Memory-bounded Schur elimination of an existing exact modular sample matrix.

Three independently restartable phases. No matrix entry is regenerated or
changed. Full rational-function gates remain in overnight_upper_probe.py.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import sys
import time

import numpy as np
from flint import nmod_mat,ctx
import overnight_upper_probe as base

ctx.threads=1
P=base.PRIME
HERE=Path(__file__).parent
PREFIX=6000


def paths(mode):
    stem=base.stem(mode)
    return stem,Path(str(stem)+'_block.json'),Path(str(stem)+'_prefix.u32'),Path(str(stem)+'_schur.u32')


def read_matrix(path,rows,cols):
    matrix=nmod_mat(rows,cols,P)
    with path.open('rb') as f:
        for i in range(rows):
            row=np.fromfile(f,dtype=np.uint32,count=cols);assert len(row)==cols
            for j,v in enumerate(row):matrix[i,j]=int(v)
    return matrix


def prefix(mode):
    started=time.monotonic();stem,meta,dp,sp=paths(mode)
    data=json.loads(stem.with_suffix('.json').read_text())
    assert data['completed_rows']==data['rows']
    rows,cols=data['rows'],data['orbit_columns']+1
    assert base.digest(stem.with_suffix('.u32'))==data['matrix_sha256']
    matrix=nmod_mat(PREFIX,cols,P)
    with stem.with_suffix('.u32').open('rb') as f:
        for i in range(PREFIX):
            row=np.fromfile(f,dtype=np.uint32,count=cols)
            for j,v in enumerate(row):matrix[i,j]=int(v)
    print('PREFIX FILLED',PREFIX,cols,'SECONDS',time.monotonic()-started,flush=True)
    reduced,rank=matrix.rref(inplace=True)
    assert rank==PREFIX
    pivots=[next(j for j in range(cols) if reduced[i,j]) for i in range(rank)]
    assert cols-1 not in pivots
    remaining=[j for j in range(cols) if j not in set(pivots)]
    with dp.open('wb') as f:
        for i in range(rank):
            np.fromiter((int(reduced[i,j]) for j in remaining),dtype=np.uint32,count=len(remaining)).tofile(f)
    out=dict(status='PREFIX_RREF_COMPLETE',mode=mode,rows=rows,cols=cols,prefix_rows=PREFIX,
             pivots=pivots,remaining=remaining,schur_rows=rows-PREFIX,schur_cols=len(remaining),
             completed_schur_rows=0,original_matrix_sha256=data['matrix_sha256'],
             prefix_sha256=base.digest(dp),producer_sha256=base.digest(Path(__file__)),
             prefix_seconds=time.monotonic()-started)
    meta.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('DONE PREFIX',rank,len(remaining),'SECONDS',out['prefix_seconds'],flush=True)


def schur(mode):
    started=time.monotonic();stem,meta,dp,sp=paths(mode);data=json.loads(meta.read_text())
    assert base.digest(dp)==data['prefix_sha256']
    r,c=data['prefix_rows'],data['schur_cols'];D=read_matrix(dp,r,c)
    done=data['completed_schur_rows'];cols=data['cols'];p=data['pivots'];q=data['remaining']
    print('SCHUR PREFIX LOADED',r,c,'RESUME',done,'SECONDS',time.monotonic()-started,flush=True)
    with stem.with_suffix('.u32').open('rb') as source,sp.open('r+b' if sp.exists() else 'w+b') as dest:
        for start in range(done,data['schur_rows'],512):
            count=min(512,data['schur_rows']-start)
            source.seek((r+start)*cols*4)
            raw=np.fromfile(source,dtype=np.uint32,count=count*cols).reshape(count,cols)
            B=nmod_mat(count,r,P);C=nmod_mat(count,c,P)
            for i in range(count):
                for j,v in enumerate(raw[i,p]):B[i,j]=int(v)
                for j,v in enumerate(raw[i,q]):C[i,j]=int(v)
            result=C-B*D
            dest.seek(start*c*4)
            for i in range(count):
                np.fromiter((int(result[i,j]) for j in range(c)),dtype=np.uint32,count=c).tofile(dest)
            dest.flush();done=start+count;data['completed_schur_rows']=done
            meta.write_text(json.dumps(data,separators=(',',':'))+'\n')
            print('SCHUR ROWS',done,'SECONDS',time.monotonic()-started,flush=True)
            del raw,B,C,result
            if time.monotonic()-started>1050:break
    if done==data['schur_rows']:
        data.update(status='SCHUR_COMPLETE',schur_sha256=base.digest(sp))
    data['schur_seconds_this_run']=time.monotonic()-started
    meta.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],flush=True)


def finish(mode):
    started=time.monotonic();stem,meta,dp,sp=paths(mode);block=json.loads(meta.read_text())
    assert block['status']=='SCHUR_COMPLETE' and base.digest(sp)==block['schur_sha256']
    r,c=block['prefix_rows'],block['schur_cols'];q=block['remaining'];p=block['pivots']
    matrix=read_matrix(sp,block['schur_rows'],c)
    print('SCHUR FILLED','SECONDS',time.monotonic()-started,flush=True)
    reduced,rank=matrix.rref(inplace=True)
    pivots=[next(j for j in range(c) if reduced[i,j]) for i in range(rank)]
    target_pivot=c-1 in pivots
    free=[j for j in range(c) if j not in pivots]
    selected=free if target_pivot else [c-1]
    Z=nmod_mat(c,len(selected),P)
    for k,f in enumerate(selected):
        Z[f,k]=1
        for i,j in enumerate(pivots):Z[j,k]=-reduced[i,f]
    del matrix,reduced
    print('SCHUR RANK',rank,'LIFT',len(selected),'SECONDS',time.monotonic()-started,flush=True)
    D=read_matrix(dp,r,c);V=-(D*Z);del D
    data=json.loads(stem.with_suffix('.json').read_text());width=data['orbit_columns']
    data.update(status='MODULAR_DIAGNOSTIC_ONLY',ranks=[r+rank-int(target_pivot),r+rank],
                block_certificate=meta.name,block_certificate_sha256=base.digest(meta))
    proposals=[]
    for k,f in enumerate(selected):
        vector={q[j]:int(Z[j,k]) for j in range(c) if Z[j,k]}
        vector.update({p[j]:int(V[j,k]) for j in range(r) if V[j,k]})
        rational=[]
        for j,value in sorted(vector.items()):
            coeff=base.ratrec(value,P)
            if coeff is None:rational=None;break
            rational.append([j,str(coeff)])
        proposals.append(rational)
    if target_pivot:
        data.update(kernel_free_columns=[q[j] for j in free],kernel_proposals=proposals)
    else:
        data['rational_reconstructed']=proposals[0] is not None
        if proposals[0] is not None:
            coeff=[Q(0)]*width
            for j,value in proposals[0]:
                if j<width:coeff[j]=-Q(value)
            assert dict(proposals[0])[width]=='1'
            data.update(status='RATIONAL_PROPOSAL_PENDING_EXACT_GATE',coefficient_proposal=list(map(str,coeff)))
    data['block_solve_seconds']=time.monotonic()-started
    stem.with_suffix('.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE RANKS',data['ranks'],'RECONSTRUCTED',sum(v is not None for v in proposals),'/',len(proposals),
          'SECONDS',data['block_solve_seconds'],flush=True)


if __name__=='__main__':globals()[sys.argv[2]](sys.argv[1])
