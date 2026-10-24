#!/usr/bin/env python3
"""Complete NC8 probe with32-frequency vector batches and a reusable row cache.
Budget480s, checkpoint after every batch; same family, prime and seed as before.
Memory: one uint32 disk-backed row matrix, one FLINT matrix, batched vectors.
"""
import json,time,math,random,sys
from pathlib import Path
import numpy as np
from flint import nmod_mat
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'trees/all_tree_dfs'))
from nc_top import ratrec
HERE=Path(__file__).parent;P=1000003;n=8;start=time.time();d=json.loads((HERE/'nc_marked_paths_8_family.json').read_text());uu=d['units'];oo=d['orbits'];m=len(oo);nr=m+30;nc=m+1
masks=np.array([[sum(1<<i for i in side) for side,s in u['cuts']] for u in uu],dtype=np.int64)
signs=np.array([[s for side,s in u['cuts']] for u in uu],dtype=np.int64);apex=np.array([u['apex'] for u in uu],dtype=np.int64)
member=np.array([[mask>>i&1 for i in range(n)] for mask in range(1<<n)],dtype=np.int64)
order=np.array([i for o in oo for i in o]);offset=np.cumsum([0]+[len(o) for o in oo])[:-1]
inv=np.zeros(P,dtype=np.int64);inv[1]=1
for j in range(2,P):inv[j]=P-(P//j)*inv[P%j]%P
rng=random.Random(24102412);pts=[]
for _ in range(nr):
    pp=[rng.randint(1,5)]
    for _ in range(n-2):pp.append(sum(pp)+rng.randint(1,10))
    pt=[-sum(pp)]+pp;rng.shuffle(pt);pts.append(pt)
cache=HERE/'nc_marked_rows_8.npy';state=HERE/'nc_marked_rows_8_state.json'
if cache.exists():mat=np.lib.format.open_memmap(cache,mode='r+');done=json.loads(state.read_text())['rows']
else:mat=np.lib.format.open_memmap(cache,mode='w+',dtype=np.uint32,shape=(nr,nc));done=0
print('start rows',done,'columns',nc,'setup',time.time()-start,flush=True)
for j in range(done,nr,32):
    block=pts[j:j+32];om=np.array(block,dtype=np.int64).T%P;allq=member@om%P;aa=om[apex,:];den=np.ones_like(aa)
    for k in range(n-2):
        qs=allq[masks[:,k],:];den=den*qs%P;den=den*((qs+signs[:,k,None]*aa)%P)%P
    assert np.all(den)
    numer=aa*aa%P;numer=numer*numer%P
    vv=numer*inv[den]%P;rows=np.add.reduceat(vv[order,:],offset,axis=0).T%P
    mat[j:j+len(block),:-1]=rows
    mat[j:j+len(block),-1]=[(-1)*pow(math.prod(p)%P,P-2,P)%P for p in block]
    mat.flush();state.write_text(json.dumps(dict(rows=j+len(block),shape=[nr,nc],seed=24102412,prime=P)))
    if j%320==0:print('rows',j+len(block),'seconds',time.time()-start,flush=True)
    if time.time()-start>420:raise TimeoutError('generation budget with checkpoint')
# Construct from blocks, avoiding a full Python integer matrix.
print('FLINT load',time.time()-start,flush=True);M=nmod_mat(nr,nc,P)
for i in range(nr):
    for j,x in enumerate(mat[i].tolist()):M[i,j]=x
    if (i+1)%1000==0:print('loaded',i+1,'seconds',time.time()-start,flush=True)
print('RREF',nr,nc,'seconds',time.time()-start,flush=True);R,rank=M.rref(inplace=True)
piv=[next(j for j in range(nc) if R[i,j]) for i in range(rank)]
res=dict(n=n,prime=P,seed=24102412,status='MODULAR_DIAGNOSTIC_ONLY',family='old NC caterpillars + all NC source/root paths',units=len(uu),orbits=m,rows=nr,ranks=[rank-int(m in piv),rank],elapsed_seconds=time.time()-start)
if m not in piv:
    x=[0]*m
    for i,j in enumerate(piv):x[j]=int(R[i,m])
    cs=[ratrec(a,P) for a in x];res['rational_reconstructed']=sum(c is not None for c in cs)
    if all(c is not None for c in cs):res['coefficient_proposal']=[str(c) for c in cs]
else:
    free=[j for j in range(m) if j not in piv];rels=[]
    for f in free:
        rel=[(f,'1')]
        for i,j in enumerate(piv):
            if j==m:continue
            x=-int(R[i,f])%P
            if x:
                c=ratrec(x,P)
                if c is None:rel=None;break
                rel.append((j,str(c)))
        rels.append(rel)
    res.update(free_columns=free,kernel_proposals=rels)
(HERE/'nc_marked_paths_8.json').write_text(json.dumps(res,indent=2)+'\n');print('DONE',res['ranks'],'seconds',res['elapsed_seconds'],flush=True)
