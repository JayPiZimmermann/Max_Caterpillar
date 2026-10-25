"""Target sequence diagnostic after the proved twelve-term function identity.

Uses only the existing feature alphabet; finite target values are not an
eventual-zero proof. Exact Boolean-cube sums avoid enumerating non-PM cuts.
"""
from pathlib import Path
import itertools,json,math,time
import numpy as np
from overnight_uniform_fay import HERE,KEYS,vec,P
from overnight_uniform_fay_global_gate import nullspace

def cube_target(q):
    N=2*q+1;out=[0]*288
    for b in itertools.product((0,1),repeat=q):
        cuts=set(range(2,2*q-1,2))|{2*j+1 for j in range(q)if b[j]};E=[]
        for j in range(1,2*q):E.append((max([0]+[k for k in cuts if k<j])+1,j+1))
        v=vec({'root':max(cuts)+1,'edges':E});sgn=(-1)**(N+len(cuts))
        for k in range(288):out[k]+=sgn*int(v[k])
    return out

def main():
    start=time.monotonic();L=json.loads((HERE/'overnight_uniform_fay_analyze.json').read_text());K=np.array(L['integer_nullspace_columns'],dtype=np.int64).T;D=json.loads((HERE/'overnight_uniform_fay_global_gate.json').read_text());C=D['global_constraints_on_local_nullspace'];inventory=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());rel=json.loads((HERE/'overnight_uniform_fay_candidate.json').read_text())['gate']['smallest_violated_sampled_relation'];r=np.zeros(288,dtype=np.int64)
    for j,c in rel.items():r+=(c if c<P//2 else c-P)*vec(inventory['units'][int(j)])
    C.append(list(map(int,r@K%P)));V,rank=nullspace(np.array(C,dtype=np.int64));A=(K%P)@V%P;responses=[];targets={}
    for q in range(2,11):
        t=cube_target(q);targets[str(q)]=t;response=np.array([x%P for x in t],dtype=np.int64)@A%P;responses.append(response);print('q',q,'target_detectable',bool(np.any(response)),'seconds',time.monotonic()-start,flush=True)
    candidates=[]
    for j in range(A.shape[1]):
        seq=[int(r[j])for r in responses]
        if any(seq):candidates.append({'coefficient_column':j,'coefficients_mod':{KEYS[i]:int(v)for i,v in enumerate(A[:,j])if v},'sequence_q2_to_q10_mod':seq})
    candidates.sort(key=lambda x:len(x['coefficients_mod']));out={'status':'MODULAR_SEQUENCE_GATE_AFTER_EXACT_FUNCTION_IDENTITY','local_nullity':K.shape[1],'additional_constraint_rank_mod':rank,'coefficient_nullity_mod':V.shape[1],'twelve_term_constraint_exact':list(map(int,r)),'exact_signed_caterpillar_vectors':targets,'all_tested_targets_zero_mod':not bool(candidates),'candidates':candidates[:5],'scope':'The12-term relation is an exact whole-function identity. N7 global constraints still come from a modular necessary gate. Finite target-sequence values do not prove eventual vanishing or descent.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',out['all_tested_targets_zero_mod'],out['seconds'],flush=True)

if __name__=='__main__':main()
