#!/usr/bin/env python3
"""Memory-bounded exact chamber matrix for the descent-limited upper test.
All coefficients integer, crossing forms primitive integral. LP proposes;
selected coefficients are rationally reconstructed and every integer row is
then checked exactly. Run with repository venv Python: sparse_upper.py N mode.
"""
import sys,itertools,math,json,time,gc
from array import array
from pathlib import Path
from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix,save_npz,load_npz
from scipy.optimize import linprog
from cyclic_upper import family

def build(n,keys):
    k=len(keys);pairs=list(itertools.combinations(range(n),2));nv=k+n+len(pairs)
    ri=array('i');ci=array('i');va=array('i');rhs=[];rows=0
    for chno,ch in enumerate(itertools.permutations(range(n))):
        pos={v:i for i,v in enumerate(ch)};lin=[{} for _ in range(n)];cross={}
        for j,(h,M) in enumerate(keys):
            a=list(h)
            for u,v in M:
                if pos[u]<pos[v]:a[u]+=1;a[v]-=1
            D=[];tot=0
            for u in ch[:-1]:tot+=a[u];D.append(tot)
            positive=any(t>0 for t in D);negative=any(t<0 for t in D)
            if positive and negative:
                g=math.gcd(*a);first=next(t for t in D if t);sgn=1 if first>0 else -1
                key=tuple(sgn*t//g for t in D);cross.setdefault(key,{})[j]=g
                if sgn<0:
                    for u,t in enumerate(a):
                        if t:lin[u][j]=t
            elif positive:
                for u,t in enumerate(a):
                    if t:lin[u][j]=t
        block=[(d,0) for d in cross.values()]
        for u,d in enumerate(lin):
            d[k+u]=1
            for pi,(a,b) in enumerate(pairs):
                if u==(a if pos[a]<pos[b] else b):d[k+n+pi]=1
            block.append((d,int(u==ch[0])))
        for d,b in block:
            for j,v in d.items():ri.append(rows);ci.append(j);va.append(v)
            rhs.append(b);rows+=1
        if (chno+1)%100==0:print('chambers',chno+1,'rows',rows,'nnz',len(va),flush=True)
    A=coo_matrix((np.frombuffer(va,dtype=np.int32),(np.frombuffer(ri,dtype=np.int32),np.frombuffer(ci,dtype=np.int32))),shape=(rows,nv)).tocsr()
    return A,np.array(rhs,dtype=np.int32)

def main():
    n=int(sys.argv[1]);mode=sys.argv[2];folder=Path(__file__).parent
    keys=family(n,mode=='dihedral',int(mode[4:]) if mode.startswith('desc') else None)
    print(n,mode,'units',len(keys),flush=True);name=f'sparse_{n}_{mode}'
    if (folder/(name+'.npz')).exists():
        A=load_npz(folder/(name+'.npz'));b=np.load(folder/(name+'_rhs.npy'))
    else:
        A,b=build(n,keys);save_npz(folder/(name+'.npz'),A);np.save(folder/(name+'_rhs.npy'),b)
    print('MATRIX',A.shape,A.nnz,flush=True);gc.collect()
    res=linprog(np.zeros(A.shape[1]),A_eq=A.astype(float),b_eq=b,bounds=[(None,None)]*A.shape[1],method='highs',options={'time_limit':300})
    print('LP',res.status,res.message,flush=True)
    data={'n':n,'mode':mode,'units':len(keys),'rows':A.shape[0],'status':int(res.status)}
    if res.success:
        x=[Fraction(float(v)).limit_denominator(10**7) for v in res.x]
        supp=[j for j,v in enumerate(x) if v];B=A[:,supp].tocsr();xx=[x[j] for j in supp]
        bad=[]
        for i in range(B.shape[0]):
            row=B.getrow(i)
            if sum(int(v)*xx[int(j)] for j,v in zip(row.indices,row.data))!=int(b[i]):bad.append(i)
        print('EXACT bad',len(bad),'neurons',sum(bool(v) for v in x[:len(keys)]),flush=True)
        data['exact_bad']=len(bad)
        if not bad:
            data['neurons']=[{'head':h,'M':M,'coefficient':str(x[j])} for j,(h,M) in enumerate(keys) if x[j]]
            data['aux']=[str(v) for v in x[len(keys):]]
    (folder/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
