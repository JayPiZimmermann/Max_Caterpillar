"""Intersect exact local-compatible scores with full N5/N7 evaluation gates.

N5 data are exact rational evaluations; N7 data are modular. These gates
are necessary diagnostics, not independently proved all-frequency relations.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time
import numpy as np
from overnight_uniform_fay import HERE,KEYS,vec,P
from flint import nmod_mat,ctx

def qmod(s):q=Q(str(s));return q.numerator*pow(q.denominator,-1,P)%P
def nullspace(A):
    R,rank=nmod_mat(A.tolist(),P).rref();width=A.shape[1];piv=[];at=0
    for i in range(rank):
        while not R[i,at]:at+=1
        piv.append(at);at+=1
    K=[]
    for j in range(width):
        if j in piv:continue
        v=[0]*width;v[j]=1
        for i,k in enumerate(piv):v[k]=-int(R[i,j])%P
        K.append(v)
    return np.array(K,dtype=np.int64).T,rank

def main():
    ctx.threads=1;start=time.monotonic();local=json.loads((HERE/'overnight_uniform_fay_analyze.json').read_text());D=json.loads((HERE/'overnight_uniform_fay.json').read_text());K=np.array(local['integer_nullspace_columns'],dtype=np.int64).T;constraints=[];gates={};relations={}
    for N in(5,7):
        name='overnight_uniform_pruning_signed_gate'if N==5 else'overnight_uniform_pruning_signed7';data=json.loads((HERE/(name+'.json')).read_text());units=data['units'];F=np.array([vec(u)for u in units],dtype=np.int64)@K
        E=np.array([[qmod(x)for x in r]for r in data['rows']],dtype=np.int64)if N==5 else np.fromfile(HERE/(name+'.u32'),dtype='<u4').reshape(data['rows'],len(units)+1).astype(np.int64)
        R,rank=nmod_mat(E[:,:-1].tolist(),P).rref();piv=[];at=0
        for i in range(rank):
            while not R[i,at]:at+=1
            piv.append(at);at+=1
        gs=[];rels=[]
        for j in range(len(units)):
            if j in piv:continue
            row=F[j].copy();rel={j:1}
            for i,k in enumerate(piv):
                c=int(R[i,j]);row=(row-c*F[k])%P
                if c:rel[k]=-c%P
            gs.append(row);rels.append(rel)
        constraints.extend(gs);V,cr=nullspace(np.array(constraints,dtype=np.int64));T={n:(np.array(t,dtype=np.int64)@K@V)%P for n,t in D['targets'].items()};gates[N]={'evaluation_rank_mod':rank,'new_relation_rows':len(gs),'joint_constraint_rank_mod':cr,'coefficient_nullity_mod':V.shape[1],'target_detectable_mod':{n:bool(np.any(t))for n,t in T.items()}};relations[N]=rels;print('gate',N,gates[N],flush=True)
    candidates=[]
    for j in range(V.shape[1]):
        coeff=(K@V[:,j])%P;response={n:int(t[j])for n,t in T.items()}
        if any(response.values()):candidates.append({'coefficients_mod':{KEYS[i]:int(v)for i,v in enumerate(coeff)if v},'responses_mod':response})
    candidates.sort(key=lambda x:(not all(x['responses_mod'].values()),len(x['coefficients_mod'])))
    out={'status':'MODULAR_LOCAL_PLUS_FULL_N5_N7_GATE','prime':P,'exact_local_nullity':K.shape[1],'gates':gates,'candidates':candidates[:5],'global_constraints_on_local_nullspace':[list(map(int,r))for r in constraints],'global_evaluation_relations':relations,'scope':'N7 relation rows are finite-field necessary tests only. A failed candidate needs an independently proved rational identity before a refutation. Local nullspace is exact and exhaustively checked separately.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('CANDIDATES',len(candidates),'seconds',out['seconds'],flush=True)

if __name__=='__main__':main()
