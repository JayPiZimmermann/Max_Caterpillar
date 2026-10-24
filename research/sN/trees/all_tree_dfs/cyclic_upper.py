#!/usr/bin/env python3
"""Try exponentially sized caterpillar dictionaries from cyclic label orders.
Uses exact chamber equations from construct/nonsym.py, floating LP to find
candidate, then exact Fraction validation on every chamber equation.
Command: research/sN/dfs/h4-general-neurons/venv/bin/python this.py N [dihedral]
No random filters; all cuts and all 3^(N-2) states included.
"""
import sys,itertools,json,time
from pathlib import Path
from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'construct'))
from nonsym import exact_rows

def family(n,dihedral=False,descents=None):
    orders={tuple((i+a)%n for i in range(n)) for a in range(n)}
    if dihedral:orders|={tuple(reversed(p)) for p in list(orders)}
    if descents is not None:
        orders={p for p in itertools.permutations(range(n)) if sum(p[i]>p[i+1] for i in range(n-1))<=descents}
    out=set();r=n-2
    for pi in sorted(orders):
        for mask in range(1,1<<r):
            S=[j for j in range(1,r+1) if mask>>(j-1)&1];q=max(S)
            edges=[(pi[max([s for s in S if s<j],default=0)+1],pi[j+1]) for j in range(1,r+1)]
            head=[0]*n;head[pi[q+1]]=1;head[pi[0]]=-1
            for states in itertools.product(range(3),repeat=r):
                h=head.copy();M=[]
                for (i,j),t in zip(edges,states):
                    if t==1 or (t==2 and i>j):h[i]+=1;h[j]-=1
                    if t==2:M.append(tuple(sorted((i,j))))
                out.add((tuple(h),tuple(sorted(M))))
    return sorted(out)

def main():
    n=int(sys.argv[1]); mode=sys.argv[2] if len(sys.argv)>2 else "cyclic"
    dihedral=mode=="dihedral";descents=int(mode[4:]) if mode.startswith("desc") else None;start=time.time()
    keys=family(n,dihedral,descents);neurons=[(h,dict.fromkeys(M,1)) for h,M in keys]
    print(n,'mode',mode,'units',len(keys),flush=True)
    eqs,nv=exact_rows(n,neurons)
    print('rows',len(eqs),'variables',nv,'seconds',time.time()-start,flush=True)
    I=[];J=[];V=[]
    for i,(d,b) in enumerate(eqs):
        for j,c in d.items():I.append(i);J.append(j);V.append(float(c))
    A=coo_matrix((V,(I,J)),shape=(len(eqs),nv)).tocsr();b=np.array([float(t) for _,t in eqs])
    res=linprog(np.zeros(nv),A_eq=A,b_eq=b,bounds=[(None,None)]*nv,method='highs')
    print('LP',res.status,res.message,flush=True)
    data={'n':n,'mode':mode,'units':len(keys),'rows':len(eqs),'lp_status':int(res.status)}
    if res.success:
        x=[Fraction(float(v)).limit_denominator(10**6) for v in res.x]
        bad=[i for i,(d,b) in enumerate(eqs) if sum(c*x[j] for j,c in d.items())!=b]
        print('EXACT validation failures',len(bad),'support',sum(bool(v) for v in x[:len(keys)]),flush=True)
        data['exact_failures']=len(bad)
        if not bad:
            data['coefficients']=[{'head':h,'M':M,'coefficient':str(x[i])} for i,(h,M) in enumerate(keys) if x[i]]
            data['aux']=[str(v) for v in x[len(keys):]]
    Path(__file__).with_name(f'cyclic_upper_{n}_{mode}.json').write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
