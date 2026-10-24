#!/usr/bin/env python3
"""Test whether the first noncaterpillar shape repairs NC8.

Adds every noncrossing subdivided-claw unit oriented away from a source,
with arbitrary marked root, to the old NC caterpillar family. Finite-field
elimination proposes a coefficient vector; only a later exact rational gate
can certify a positive result. Domain: all4979 deterministic frequency rows.
"""
import json,time,random,math,gzip
from pathlib import Path
import numpy as np
from flint import nmod_mat
from nc_top import ratrec
P=1000003;HERE=Path(__file__).parent

def evaluator(units,orbits,n=8):
    masks=np.array([[sum(1<<i for i in side) for side,s in u['cuts']] for u in units],dtype=np.int64)
    signs=np.array([[s for side,s in u['cuts']] for u in units],dtype=np.int64)
    apex=np.array([u['apex'] for u in units],dtype=np.int64)
    membership=np.array([[int(mask>>i&1) for i in range(n)] for mask in range(1<<n)],dtype=np.int64)
    order=np.array([i for o in orbits for i in o]);offset=np.cumsum([0]+[len(o) for o in orbits])[:-1]
    inv=np.zeros(P,dtype=np.int64);inv[1]=1
    for j in range(2,P):inv[j]=P-(P//j)*inv[P%j]%P
    def ev(pt):
        om=np.array(pt,dtype=np.int64)%P;qs=(membership@om)[masks]%P;aa=om[apex]
        den=np.ones(len(units),dtype=np.int64)
        for j in range(n-2):den=den*qs[:,j]%P;den=den*((qs[:,j]+signs[:,j]*aa)%P)%P
        assert np.all(den)
        numer=np.ones(len(units),dtype=np.int64)
        for _ in range(n-4):numer=numer*(-aa)%P
        vv=numer*inv[den]%P;return [int(t) for t in np.add.reduceat(vv[order],offset)%P]
    return ev

def main():
    start=time.time();path=HERE/'nc_fast_8.json'
    with (path.open() if path.exists() else gzip.open(str(path)+'.gz','rt')) as f:d=json.load(f)
    claw=json.loads((HERE.parent/'dfs_review_nc8_claw.json').read_text())
    m=len(d['orbits'])+len(claw['orbits']);pts=d['points'];rows=d['rows'];rng=random.Random(241031)
    while len(pts)<m+30:
        pp=[rng.randint(1,5)]
        for _ in range(6):pp.append(sum(pp)+rng.randint(1,10))
        pt=[-sum(pp)]+pp;rng.shuffle(pt);pts.append(pt)
    old_ev=evaluator(d['units'],d['orbits']);new_ev=evaluator(claw['units'],claw['orbits'])
    old_count=len(rows)
    for j,pt in enumerate(pts):
        old=rows[j][:-1] if j<old_count else old_ev(pt)
        new=new_ev(pt);target=(-1)*pow(math.prod(pt)%P,P-2,P)%P
        row=old+new+[target]
        if j<old_count:rows[j]=row
        else:rows.append(row)
        if (j+1)%500==0:print('rows',j+1,'elapsed',time.time()-start,flush=True)
    print('RREF',len(rows),m+1,flush=True);M=nmod_mat(rows,P);R,rank=M.rref(inplace=True)
    piv=[next(j for j in range(m+1) if R[i,j]) for i in range(rank)]
    out={'n':8,'prime':P,'rows':len(rows),'old_orbits':len(d['orbits']),'new_orbits':len(claw['orbits']),
         'modular_ranks':[rank-int(m in piv),rank],'status':'MODULAR_DIAGNOSTIC_ONLY','new_points':pts[old_count:]}
    if m not in piv:
        x=[0]*m
        for i,j in enumerate(piv):x[j]=int(R[i,m])
        cs=[ratrec(a,P) for a in x]
        if all(c is not None for c in cs):out['coefficient_proposal']=[str(c) for c in cs]
        print('reconstructed',sum(c is not None for c in cs),'of',m,flush=True)
    out['elapsed_seconds']=time.time()-start
    (HERE/'nc_claw_extended_8.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',out['modular_ranks'],'elapsed',time.time()-start,flush=True)
if __name__=='__main__':main()
