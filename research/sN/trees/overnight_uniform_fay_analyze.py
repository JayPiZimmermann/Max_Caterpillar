"""Exact nullspace and exhaustive local compatibility for the fixed alphabet."""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time
import numpy as np
from overnight_uniform_fay import HERE,KEYS,vec,structure,rewires,family,P
from flint import fmpq_mat,nmod_mat,ctx

def main():
    ctx.threads=1;start=time.monotonic();D=json.loads((HERE/'overnight_uniform_fay.json').read_text());rows=D['independent_constraint_rows'];C=fmpq_mat(rows);R,rank=C.rref();assert rank==len(rows);piv=[];at=0
    for i in range(rank):
        while not R[i,at]:at+=1
        piv.append(at);at+=1
    K=[]
    for j in range(288):
        if j in piv:continue
        v=[Q(0)]*288;v[j]=Q(1)
        for i,k in enumerate(piv):v[k]=-Q(str(R[i,j]))
        den=math.lcm(*(q.denominator for q in v));K.append([int(den*q)for q in v])
    K=np.array(K,dtype=np.int64).T;assert not np.any(np.array(rows,dtype=np.int64)@K)
    bound=int(np.max(np.abs(K)));print('rank',rank,'nullity',K.shape[1],'maxcoeff',bound,flush=True)
    targets={n:np.array(t,dtype=np.int64)for n,t in D['targets'].items()};responses={n:t@K for n,t in targets.items()};candidates=[]
    for j in range(K.shape[1]):
        resp={n:int(v[j])for n,v in responses.items()}
        if any(resp.values()):candidates.append({'column':j,'terms':int(np.count_nonzero(K[:,j])),'coefficients':{KEYS[i]:int(v)for i,v in enumerate(K[:,j])if v},'signed_caterpillar_responses':resp})
    candidates.sort(key=lambda x:(not all(x['signed_caterpillar_responses'].values()),x['terms'],sum(abs(x)for x in x['coefficients'].values())))
    units={5:family(5,'all'),7:family(7,'all'),9:json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text())['units']};checked=0;assignment_rows=[];arity_rows={};maxrow=0
    for N,us in units.items():
        arity_rows[N]=[]
        for U in us:
            f=vec(U);assert int(np.max(np.abs(f)))*288*bound<2**63
            z=f@K;assignment_rows.append(z);arity_rows[N].append(z)
            E=list(map(tuple,U['edges']));V,T,_,_=structure(tuple(sorted(tuple(sorted(e))for e in E)));root=U['root'];parent={root:None};todo=[root]
            for r in todo:
                for v in T[r]:
                    if v!=parent[r]:parent[v]=r;todo.append(v)
            for r in todo:
                for v,w in itertools.combinations(sorted(v for v in T[r]if v!=parent[r]),2):
                    terms=rewires({'root':root,'edges':E},r,v,w);row=sum((c*vec(u)for c,u in terms),np.zeros(288,dtype=np.int64));maxrow=max(maxrow,int(np.max(np.abs(row))));assert maxrow*288*bound<2**63
                    assert not np.any(row@K),'Unselected integer constraint not spanned over Q';checked+=1
        print('checked',N,checked,'seconds',time.monotonic()-start,flush=True)
    # Modular assignment rank is labeled as such; exact candidates below have
    # already been checked against every local identity with integer arithmetic.
    ranks={str(n):nmod_mat(np.array(a,dtype=np.int64).__mod__(P).tolist(),P).rank()for n,a in arity_rows.items()};joint=nmod_mat(np.array(assignment_rows,dtype=np.int64).__mod__(P).tolist(),P).rank()
    out={'status':'EXACT_ALL_LOCAL_CONSTRAINTS_CHARACTERIZED','feature_count':288,'constraint_rank_over_Q':rank,'coefficient_nullity':K.shape[1],'all_local_identities_checked_exactly':checked,'integer_nullspace_columns':K.T.tolist(),'nullspace_integer_max_abs':bound,'constraint_max_abs':maxrow,'int64_product_bound':maxrow*288*bound,'assignment_ranks_mod':ranks,'joint_assignment_rank_mod':joint,'candidates':candidates[:8],'scope':'Every displayed candidate satisfies all local graft relations at N5,N7,N9 exactly. Its signed caterpillar sums are necessary target responses only. This does not establish rational-kernel descent or a separator. Assignment dimensions are modular diagnostics. No new features.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('integer_nullspace_columns',)},indent=2),flush=True)

if __name__=='__main__':main()
