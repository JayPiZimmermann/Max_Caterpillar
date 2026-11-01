"""Small exact-pattern positive-fold search on the48-function F4 orbit.

The LP proposes coefficients only. Every accepted folding is checked by
rational evaluation on every ray of the complete24-wall arrangement.
No hidden-layer width search or sampled fitting is used.
"""
import hashlib,itertools,json,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def main():
    start=time.monotonic();data=json.loads(Path('overnight_fixed_f4_inventory.json').read_text());F=[tuple(tuple(r)for r in f)for f in data['functions']];index={f:i for i,f in enumerate(F)};frame=data['frame_of_function'];base=data['base_function'];R=np.asarray(data['rays'],dtype=np.int64);H=np.asarray(data['hyperplanes'],dtype=np.int64);Phi=np.c_[R,abs(R@H.T)];values=[];closed=[]
    for A in F:
        v=R@np.asarray(A,dtype=np.int64).T;values.append(np.maximum(np.min(v,axis=1),0));closed.append(np.min(v,axis=1)>=0)
    values=np.asarray(values,dtype=np.int64).T;closed=np.asarray(closed).T;actions=[]
    for p in itertools.permutations(range(4)):
        actions.append([index[tuple(sorted(tuple(row[p[j]]for j in range(4))for row in A))]for A in F])
    others=[i for i in range(3)if i!=frame[base]];one=[i for i in range(48)if frame[i]==others[0]];two=[i for i in range(48)if frame[i]==others[1]];reps={}
    for i,j in itertools.product(one,two):
        key=min(tuple(sorted((a[i],a[j])))for a in actions);reps.setdefault(key,(i,j))
    records=[];folds=[]
    # Exact linear-ReLU control for the same feature/ray convention.
    coeff=[Q(1)]+[Q(0)]*27;assert all(max(sum(c*int(f)for c,f in zip(coeff,row)),Q(0))==max(Q(int(x[0])),Q(0))for x,row in zip(R,Phi))
    for ci,(i,j)in enumerate(reps.values()):
        ids=[base,i,j];inside=np.any(closed[:,ids],axis=1);E=np.c_[Phi[inside],-values[inside,i],-values[inside,j],np.zeros(sum(inside))];b=values[inside,base];I=np.c_[Phi[~inside],np.zeros((sum(~inside),3))];extra=np.zeros((2,31));extra[0,28]=-1;extra[1,29]=-1;extra[:,30]=1;I=np.r_[I,extra];objective=np.r_[np.zeros(30),-1];r=linprog(objective,A_eq=E,b_eq=b,A_ub=I,b_ub=np.zeros(len(I)),bounds=[(None,None)]*28+[(0,None),(0,None),(0,1)],method='highs');record={'case':ci,'functions':ids,'solver_status':r.status,'message':r.message}
        if r.x is not None and r.x[30]>1e-8:
            x=[Q(float(c)).limit_denominator(1000000)for c in r.x];weights=[Q(1),x[28],x[29]];assert all(w>0 for w in weights)
            for q,row in enumerate(Phi):
                g=sum(c*int(f)for c,f in zip(x[:28],row));target=sum(w*int(values[q,k])for w,k in zip(weights,ids));assert max(g,Q(0))==target
                if inside[q]:assert g==target
                else:assert g<=0
            fold={'functions':ids,'weights':list(map(str,weights)),'shallow_coefficients':list(map(str,x[:28])),'normalization':'Function values use twice the unit-length frame rows; divide both sides by2 for the canonical q4 functions.'};folds.append(fold);record.update(status='EXACT_POSITIVE_FOLD',weights=fold['weights'])
        else:record['status']='NO_STRICT_POSITIVE_FOLD_FOUND'
        records.append(record);print(json.dumps(record),flush=True)
    report={'status':'FINITE_THREE_FRAME_FOLD_SEARCH_COMPLETE','base_function':base,'raw_triples':256,'stabilizer_orbits':len(reps),'exact_folds':folds,'records':records,'positive_control':'EXACT_LINEAR_RELU_RAY_CONTROL_PASS','seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_f4_folds.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('records','exact_folds')}),flush=True)

if __name__=='__main__':main()
