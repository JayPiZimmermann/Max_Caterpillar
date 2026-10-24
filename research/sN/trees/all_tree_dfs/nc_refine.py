#!/usr/bin/env python3
"""Complete the budgeted NC diagnostic using exact finite-field elimination.

Requires python-flint (used only to propose coefficients, never to certify a
real identity). Add 150 deterministic fresh frequency rows, seed241030.
Input/shape enumeration is preserved in nc_fast_N.json. Output records ranks
and a rational-reconstruction proposal; rational_identity.py is the exact gate.
"""
import sys,json,time,random,math,gzip
from pathlib import Path
import numpy as np
from flint import nmod_mat
from nc_top import ratrec

def main():
    n=int(sys.argv[1]);here=Path(__file__).parent;path=here/f'nc_fast_{n}.json';start=time.time()
    with (path.open() if path.exists() else gzip.open(str(path)+'.gz','rt')) as f:d=json.load(f)
    units=d['units'];orbits=d['orbits'];P=d['prime'];m=len(orbits);rows=d['rows']
    masks=np.array([[sum(1<<i for i in side) for side,s in u['cuts']] for u in units],dtype=np.int64)
    signs=np.array([[s for side,s in u['cuts']] for u in units],dtype=np.int64)
    apex=np.array([u['apex'] for u in units],dtype=np.int64)
    membership=np.array([[int(mask>>i&1) for i in range(n)] for mask in range(1<<n)],dtype=np.int64)
    order=np.array([i for o in orbits for i in o]);offset=np.cumsum([0]+[len(o) for o in orbits])[:-1]
    inv=np.zeros(P,dtype=np.int64);inv[1]=1
    for j in range(2,P):inv[j]=P-(P//j)*inv[P%j]%P
    rng=random.Random(241030);extra=[]
    for _ in range(150):
        pos=[rng.randint(1,5)]
        for _ in range(n-2):pos.append(sum(pos)+rng.randint(1,10))
        pt=[-sum(pos)]+pos;rng.shuffle(pt);om=np.array(pt,dtype=np.int64)%P
        qs=(membership@om)[masks]%P;aa=om[apex];den=np.ones(len(units),dtype=np.int64)
        for j in range(n-2):den=den*qs[:,j]%P;den=den*((qs[:,j]+signs[:,j]*aa)%P)%P
        assert np.all(den)
        numer=np.ones(len(units),dtype=np.int64)
        for _ in range(n-4):numer=numer*(-aa)%P
        vv=numer*inv[den]%P;row=np.add.reduceat(vv[order],offset)%P
        tar=int((-1)**(n-1)*inv[math.prod(pt)%P]%P)
        rows.append([int(t) for t in np.r_[row,tar]]);extra.append(pt)
    print('RREF',len(rows),m+1,'elapsed',time.time()-start,flush=True)
    A=nmod_mat(rows,P);R,rank=A.rref(inplace=True)
    pivots=[]
    for i in range(rank):
        pivots.append(next(j for j in range(m+1) if R[i,j]))
    rankA=rank-int(m in pivots);result={'n':n,'prime':P,'rows':len(rows),'orbits':m,'extra_points':extra,
        'modular_ranks':[rankA,rank],'status':'MODULAR_DIAGNOSTIC_ONLY'}
    print('ranks',rankA,rank,'elapsed',time.time()-start,flush=True)
    if m in pivots:
        free=[j for j in range(m) if j not in pivots];relations=[]
        for f in free:
            rel=[(f,'1')];ok=True
            for i,j in enumerate(pivots):
                if j==m:continue
                a=-int(R[i,f])%P
                if not a:continue
                c=ratrec(a,P)
                if c is None:ok=False;break
                rel.append((j,str(c)))
            relations.append(rel if ok else None)
        result['free_columns']=free;result['kernel_proposals']=relations
        print('kernel proposals',len(relations),'failed',sum(r is None for r in relations),
              'sizes',[len(r) if r is not None else -1 for r in relations],flush=True)
    if m not in pivots:
        x=[0]*m
        for i,j in enumerate(pivots):x[j]=int(R[i,m])
        cc=[ratrec(a,P) for a in x]
        if all(c is not None for c in cc):result['coefficient_proposal']=[str(c) for c in cc]
        print('reconstructed',sum(c is not None for c in cc),'of',m,flush=True)
    result['elapsed_seconds']=time.time()-start
    (here/f'nc_refined_{n}.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
