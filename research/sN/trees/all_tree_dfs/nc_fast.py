#!/usr/bin/env python3
"""Budgeted dihedral Fourier diagnostic for noncrossing caterpillars.

No fixed-arity result is promoted from modular arithmetic alone. Budget:
180 seconds after family generation, at most orbit_count+30 rows, seed241028.
Vectorized tree-cut sums avoid factorial permutation symmetrization.
"""
import sys,json,time,random,math
from pathlib import Path
import numpy as np
from upper_fourier import family
from nc_top import key,ratrec
P=1000003

def main():
    n=int(sys.argv[1]);start=time.time();units=family(n,None,True,False)
    index={key(u,n):i for i,u in enumerate(units)};seen=set();orbits=[]
    for i,u in enumerate(units):
        if i in seen:continue
        orb={index[key(u,n,[(sg*j+a)%n for j in range(n)])] for sg in (-1,1) for a in range(n)}
        seen|=orb;orbits.append(sorted(orb))
    print('n',n,'units',len(units),'dihedral orbits',len(orbits),'generation sec',time.time()-start,flush=True)
    masks=np.array([[sum(1<<i for i in side) for side,s in u['cuts']] for u in units],dtype=np.int64)
    signs=np.array([[s for side,s in u['cuts']] for u in units],dtype=np.int64)
    apex=np.array([u['apex'] for u in units],dtype=np.int64)
    membership=np.array([[int(mask>>i&1) for i in range(n)] for mask in range(1<<n)],dtype=np.int64)
    order=np.array([i for o in orbits for i in o]);offset=np.cumsum([0]+[len(o) for o in orbits])[:-1]
    inv=np.zeros(P,dtype=np.int64);inv[1]=1
    for j in range(2,P):inv[j]=P-(P//j)*inv[P%j]%P
    basis={};pts=[];rows=[];rng=random.Random(241028);compute=time.time()
    for count in range(len(orbits)+30):
        pos=[rng.randint(1,5)]
        for _ in range(n-2):pos.append(sum(pos)+rng.randint(1,10))
        pt=[-sum(pos)]+pos;rng.shuffle(pt);om=np.array(pt,dtype=np.int64)%P
        qs=(membership@om)[masks]%P;aa=om[apex]
        den=np.ones(len(units),dtype=np.int64)
        for j in range(n-2):den=den*qs[:,j]%P;den=den*((qs[:,j]+signs[:,j]*aa)%P)%P
        assert np.all(den)
        numer=np.ones(len(units),dtype=np.int64)
        for _ in range(n-4):numer=numer*(-aa)%P
        vv=numer*inv[den]%P;row=np.add.reduceat(vv[order],offset)%P
        tar=int((-1)**(n-1)*inv[math.prod(pt)%P]%P);v=np.r_[row,tar]
        rows.append([int(t) for t in v]);pts.append(pt)
        for j,b in sorted(basis.items()):v=(v-v[j]*b)%P
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);basis[j]=v*inv[v[j]]%P
        if (count+1)%50==0:print('rows',count+1,'rank_aug',len(basis),'elapsed',time.time()-compute,flush=True)
        if time.time()-compute>180:break
    m=len(orbits);rankA=len(basis)-int(m in basis)
    data={'n':n,'prime':P,'units':units,'orbits':orbits,'points':pts,'rows':rows,
          'modular_ranks':[rankA,len(basis)],'status':'MODULAR_DIAGNOSTIC_ONLY','elapsed_seconds':time.time()-start}
    if m not in basis and len(rows)>len(basis):
        x=np.zeros(m+1,dtype=np.int64);x[-1]=-1
        for j,b in sorted(basis.items(),reverse=True):x[j]=-int(b@x)%P
        cc=[ratrec(a,P) for a in x[:-1]]
        if all(c is not None for c in cc):data['coefficient_proposal']=[str(c) for c in cc]
    Path(__file__).with_name(f'nc_fast_{n}.json').write_text(json.dumps(data,indent=2)+'\n')
    print('DONE ranks',data['modular_ranks'],'rows',len(rows),'proposal','coefficient_proposal' in data,'elapsed',time.time()-start,flush=True)
if __name__=='__main__':main()
