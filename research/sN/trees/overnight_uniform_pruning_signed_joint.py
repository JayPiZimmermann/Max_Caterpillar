"""Compare the small signed-shuffle family across N5 and N7, finite field only."""
from pathlib import Path
import json,time
import numpy as np
from overnight_lower_dp import PRIME
from overnight_uniform_pruning_signed7 import reduce,nullspace
from overnight_uniform_pruning_signed_family import score_data,features
HERE=Path(__file__).parent

def mod(x):
    from fractions import Fraction
    r=Fraction(x);return r.numerator*pow(r.denominator,-1,PRIME)%PRIME

def rank(M):return len(nullspace(np.array(M,dtype=np.int64),PRIME)[0]) # helper unused

def main():
    start=time.monotonic();items={};keys=None
    for n in(5,7):
        name='overnight_uniform_pruning_signed_gate' if n==5 else 'overnight_uniform_pruning_signed7';d=json.loads((HERE/(name+'.json')).read_text());units=d['units'];R=np.array([[mod(x) for x in r] for r in d['rows']],dtype=np.int64) if n==5 else np.fromfile(HERE/(name+'.u32'),dtype='<u4').reshape(d['rows'],len(units)+1).astype(np.int64)
        b={}
        for r in R:
            v=reduce(r,b,PRIME);nz=np.flatnonzero(v[:-1])
            if len(nz):j=int(nz[0]);b[j]=v*pow(int(v[j]),-1,PRIME)%PRIME
            else:assert v[-1]==0
        ff=[features(score_data(u,n),'kappa') for u in units];keys=list(ff[0]);F=np.array([[f[k] for f in ff] for k in keys],dtype=np.int64);rem=np.array([reduce(list(row)+[0],b,PRIME) for row in F]);items[n]=(F,rem)
    result={'status':'MODULAR_JOINT_SIGNED_FAMILY_GATE','prime':PRIME,'arity_stats':{}}
    for n,(F,rem) in items.items():
        fr=nullspace(F,PRIME)[1];cr=nullspace(rem[:,:-1].T,PRIME)[1];result['arity_stats'][n]={'feature_rank':fr,'constraint_rank':cr,'valid_assignment_dimension':fr-cr}
    C=np.concatenate([items[n][1][:,:-1] for n in(5,7)],axis=1).T;ker,cr=nullspace(C,PRIME);candidates=[]
    for v in ker:
        responses={n:int((-v@items[n][1][:,-1])%PRIME) for n in(5,7)}
        if any(responses.values()):
            first=next(r for r in responses.values() if r);v=v*pow(first,-1,PRIME)%PRIME
            candidates.append({'coefficients_mod':{k:int(v[i]) for i,k in enumerate(keys) if v[i]},'responses_mod':{n:int(r*pow(first,-1,PRIME)%PRIME) for n,r in responses.items()}})
    result['joint_constraint_rank']=cr;result['joint_candidate_count']=len(candidates)
    candidates.sort(key=lambda v:(not all(v['responses_mod'].values()),len(v['coefficients_mod'])))
    result['joint_candidates']=candidates[:3]
    # Test the short N7 formula with its rationally reconstructed coefficients.
    v=np.zeros(len(keys),dtype=np.int64)
    for key,val in {'all;d^1;parity^0;orientation^0;k_sum':-105,'all;d^1;parity^0;orientation^1;one':mod('-315/2'),'all;d^1;parity^1;orientation^0;k_sum':-315,'all;d^1;parity^1;orientation^1;one':mod('105/2')}.items():v[keys.index(key)]=val
    result['short_N7_formula']={n:{'passes':bool(np.all((v@rem[:,:-1])%PRIME==0)),'response_mod':int((-v@rem[:,-1])%PRIME)} for n,(F,rem) in items.items()}
    result['seconds']=time.monotonic()-start;Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
