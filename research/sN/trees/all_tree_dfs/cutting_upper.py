#!/usr/bin/env python3
"""Constraint generation for the cached exact chamber matrix.

Budget: at most 10 LPs, 60 seconds each; deterministic seed 241026.
Floating feasibility is only a candidate. A positive result is reconstructed
over Q and checked on every integer row of the complete chamber matrix.
"""
import sys, time, json
from pathlib import Path
from fractions import Fraction
import numpy as np
from scipy.sparse import load_npz
from scipy.optimize import linprog
from cyclic_upper import family

def main():
    n=int(sys.argv[1]); mode=sys.argv[2]; folder=Path(__file__).parent
    stem=f'sparse_{n}_{mode}'
    A=load_npz(folder/(stem+'.npz')); b=np.load(folder/(stem+'_rhs.npy'))
    keys=family(n,mode=='dihedral',int(mode[4:]) if mode.startswith('desc') else None)
    # Every chamber's linear equations have auxiliary columns. Include these
    # initially; add the crossing cancellation rows by violated residual.
    initial=np.unique(A[:,len(keys):].nonzero()[0])
    rng=np.random.default_rng(241026)
    available=np.setdiff1d(np.arange(A.shape[0]),initial)
    selected=np.unique(np.r_[initial,rng.choice(available,min(500,len(available)),replace=False)])
    data={'n':n,'mode':mode,'units':len(keys),'matrix_rows':A.shape[0],'seed':241026,'iterations':[]}
    start=time.time()
    for it in range(10):
        print('ITER',it,'rows',len(selected),'elapsed',time.time()-start,flush=True)
        res=linprog(np.zeros(A.shape[1]),A_eq=A[selected].astype(float),b_eq=b[selected],
                    bounds=[(None,None)]*A.shape[1],method='highs',options={'time_limit':60})
        row={'iteration':it,'rows':len(selected),'status':int(res.status)}
        data['iterations'].append(row)
        print('LP',res.status,res.message,flush=True)
        if not res.success:break
        residual=np.abs(A@res.x-b); bad=np.flatnonzero(residual>1e-7)
        row.update(max_residual=float(max(residual)),violated_rows=len(bad))
        print('residual',max(residual),'violations',len(bad),'support',sum(abs(res.x[:len(keys)])>1e-8),flush=True)
        if not len(bad):
            x=[Fraction(float(v)).limit_denominator(10**7) for v in res.x]
            supp=[j for j,v in enumerate(x) if v]; B=A[:,supp].tocsr(); xx=[x[j] for j in supp]
            exact_bad=[]
            for i in range(B.shape[0]):
                lo,hi=B.indptr[i:i+2]
                if sum(int(v)*xx[int(j)] for j,v in zip(B.indices[lo:hi],B.data[lo:hi]))!=int(b[i]):exact_bad.append(i)
            data['exact_bad']=len(exact_bad)
            print('EXACT bad',len(exact_bad),flush=True)
            if not exact_bad:
                data['neurons']=[{'head':h,'M':M,'coefficient':str(x[j])} for j,(h,M) in enumerate(keys) if x[j]]
                data['aux']=[str(v) for v in x[len(keys):]]
            break
        # Half the strongest residuals, half deterministic random violations.
        count=min(1000,len(bad));strong=bad[np.argsort(residual[bad])[-(count//2):]]
        rest=np.setdiff1d(bad,strong)
        extra=rng.choice(rest,min(count-len(strong),len(rest)),replace=False)
        selected=np.unique(np.r_[selected,strong,extra])
    data['elapsed_seconds']=time.time()-start
    (folder/f'cutting_upper_{n}_{mode}.json').write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
