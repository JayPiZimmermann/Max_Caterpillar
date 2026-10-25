"""Necessary linear conditions for any positive F4-orbit fold.

Equality is required only on the base orthant; everywhere else g<=F.
No coefficient bounds or support bound appear. A rational Farkas witness
would therefore exclude all positive folds containing the base copy.
"""
from fractions import Fraction as Q
import hashlib,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def main():
    started=time.monotonic();data=json.loads(Path('overnight_fixed_f4_inventory.json').read_text());R=np.array(data['rays'],dtype=int);H=np.array(data['hyperplanes'],dtype=int);P=np.c_[R,abs(R@H.T)];base=data['base_function'];V=[];C=[]
    for A in data['functions']:
        v=R@np.array(A,dtype=int).T;V.append(np.maximum(v.min(axis=1),0));C.append(v.min(axis=1)>=0)
    V=np.array(V,dtype=int).T;C=np.array(C,dtype=bool).T;other=[i for i in range(48) if i!=base];B=np.c_[P,-V[:,other]];inside=C[:,base];E=B[inside];b=V[inside,base];I=np.r_[B[~inside],np.c_[np.zeros((47,28),dtype=int),-np.eye(47,dtype=int)]];rhs=np.r_[V[~inside,base],np.zeros(47,dtype=int)];assert not any(rhs)
    r=linprog(np.zeros(75),A_eq=E,b_eq=b,A_ub=I,b_ub=rhs,bounds=[(None,None)]*75,method='highs');report={'status':'RELAXED_FOLD_DIAGNOSTIC','solver_status':r.status,'message':r.message,'equalities':len(E),'inequalities':len(I),'variables':75}
    if r.status==2:
        ne=len(E);ni=len(I);D=np.c_[E.T,-E.T,I.T];D=np.r_[D,np.r_[b,-b,np.zeros(ni)][None,:]];drhs=np.r_[np.zeros(75),-1];dual=linprog(np.ones(2*ne+ni),A_eq=D,b_eq=drhs,bounds=(0,None),method='highs');assert dual.success
        x=[Q(float(v)).limit_denominator(1000000) for v in dual.x];y=[x[i]-x[ne+i] for i in range(ne)];z=x[2*ne:]
        assert all(v>=0 for v in z)
        assert all(sum(y[i]*int(E[i,j]) for i in range(ne))+sum(z[i]*int(I[i,j]) for i in range(ni))==0 for j in range(75))
        assert sum(y[i]*int(b[i]) for i in range(ne))==-1
        cert={'equality_multipliers':[[int(k),str(y[i])] for i,k in enumerate(np.flatnonzero(inside)) if y[i]],'inequality_multipliers':[[int(k),str(z[i])] for i,k in enumerate(np.flatnonzero(~inside)) if z[i]],'weight_nonnegative_multipliers':[[other[j],str(z[len(R)-ne+j])] for j in range(47) if z[len(R)-ne+j]]}
        report.update(status='EXACT_ALL_SUPPORT_POSITIVE_FOLD_EXCLUSION',certificate=cert)
    else:
        report['candidate']=None if r.x is None else r.x.tolist()
    report.update(seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());Path('overnight_fixed_f4_relaxed_fold.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
