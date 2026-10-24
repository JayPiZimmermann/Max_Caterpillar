#!/usr/bin/env python3
"""Necessary top-quotient test for restricted-order caterpillar constructions.

Only full-hinge trees can contribute to the top quotient. Evaluate their
generic Fourier rational functions at deterministic generic frequencies.
Modular rank is diagnostic only, and never an exact impossibility certificate.
Budget: 110 seconds, at most min(columns+30, 1000) rows; seed 241026.
"""
import itertools,sys,time,json,random
from pathlib import Path
import numpy as np
P=1000003

def family(n,descent=None,noncrossing=False,pathonly=False):
    out={}
    for pi in itertools.permutations(range(n)):
        if descent is not None and sum(pi[i]>pi[i+1] for i in range(n-1))>descent:continue
        for mask in range(1,1<<(n-2)):
            if pathonly and mask!=(1<<(n-2))-1:continue
            S=[j for j in range(1,n-1) if mask>>(j-1)&1]
            apex=pi[0];root=pi[max(S)+1]
            edges=[(pi[max([s for s in S if s<j],default=0)+1],pi[j+1]) for j in range(1,n-1)]
            if noncrossing:
                ee=[sorted(e) for e in edges]
                if any(a<c<b<d or c<a<d<b for a,b in ee for c,d in ee):continue
            h=[0]*n;h[root]=1;h[apex]=-1
            for u,v in edges:
                if u>v:h[u]+=1;h[v]-=1
            key=(tuple(h),tuple(sorted(tuple(sorted(e)) for e in edges)))
            if key in out:continue
            cuts=[]
            for u,v in edges:
                seen={u};todo=[u]
                while todo:
                    w=todo.pop()
                    for x,y in edges:
                        if (x,y)==(u,v):continue
                        z=y if w==x else x if w==y else None
                        if z is not None and z not in seen:seen.add(z);todo.append(z)
                if root in seen:seen=set(range(n))-{apex}-seen;sgn=-1
                else:sgn=1
                cuts.append((tuple(sorted(seen)),sgn))
            out[key]={'apex':apex,'root':root,'edges':edges,'cuts':cuts}
    return list(out.values())

def main():
    n=int(sys.argv[1]);mode=sys.argv[2];des=int(mode) if mode.isdigit() else None
    name='desc'+mode if mode.isdigit() else mode
    start=time.time();units=family(n,des,mode.startswith('nc'),mode=='ncpath')
    print('n',n,'mode',name,'units',len(units),flush=True)
    rng=random.Random(241026);ba={};bb={};rows=[];points=[]
    def insert(v,basis):
        v=np.array(v,dtype=np.int64)%P
        for j,b in sorted(basis.items()):v=(v-v[j]*b)%P
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);basis[j]=v*pow(int(v[j]),P-2,P)%P
    for r in range(min(len(units)+30,5000)):
        positive=[rng.randint(1,5)]
        for _ in range(n-2):positive.append(sum(positive)+rng.randint(1,10))
        pt=[-sum(positive)]+positive;rng.shuffle(pt)
        row=[]
        for u in units:
            a=pt[u['apex']];den=1
            for side,sgn in u['cuts']:
                q=sum(pt[j] for j in side);den=den*q*(q+sgn*a)%P
            assert den
            row.append(pow(-a,n-4,P)*pow(den,P-2,P)%P)
        prod=1
        for x in pt:prod=prod*x%P
        tar=(-1)**(n-1)*pow(prod,P-2,P)%P
        insert(row,ba);insert(row+[tar],bb);rows.append(row+[tar]);points.append(pt)
        if (r+1)%50==0:print('rows',r+1,'ranks',len(ba),len(bb),'elapsed',time.time()-start,flush=True)
        if time.time()-start>110:break
    data=dict(n=n,descents=des,mode=name,prime=P,units=units,points=points,rows=rows,
              ranks=[len(ba),len(bb)],status='MODULAR_DIAGNOSTIC_ONLY',elapsed=time.time()-start)
    Path(__file__).with_name(f'upper_fourier_{n}_{name}.json').write_text(json.dumps(data,indent=2)+'\n')
    print('DONE ranks',data['ranks'],'elapsed',data['elapsed'],flush=True)
if __name__=='__main__':main()
