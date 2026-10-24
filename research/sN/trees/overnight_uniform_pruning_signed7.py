"""Single-thread modular quotient gate for the signed-shuffle family at N7.

No exact all-arity claim. Uses a shared full-permutation DP on all458 orbits.
"""
from pathlib import Path
import itertools,json,subprocess,time
import numpy as np
from dfs_review_fourier import family,points
from overnight_lower_dp import Compiler,PRIME
from overnight_uniform_pruning_signed_family import score_data,features
HERE=Path(__file__).parent;BASE=Path(__file__).with_suffix('')

def reduce(v,basis,p):
    v=np.array(v,dtype=np.int64)%p
    for j,b in sorted(basis.items()):
        if v[j]:v=(v-v[j]*b)%p
    return v

def nullspace(M,p):
    A=np.array(M,dtype=np.int64)%p;row=0;piv=[]
    for c in range(A.shape[1]):
        cand=np.flatnonzero(A[row:,c])
        if not len(cand):continue
        q=row+int(cand[0]);A[[row,q]]=A[[q,row]];A[row]=A[row]*pow(int(A[row,c]),-1,p)%p
        for i in range(A.shape[0]):
            if i!=row and A[i,c]:A[i]=(A[i]-A[i,c]*A[row])%p
        piv.append(c);row+=1
        if row==len(A):break
    out=[]
    for c in range(A.shape[1]):
        if c in piv:continue
        v=np.zeros(A.shape[1],dtype=np.int64);v[c]=1
        for i,j in enumerate(piv):v[j]=-A[i,c]%p
        out.append(v)
    return out,len(piv)

def main():
    start=time.monotonic();u=family(7,'all');dag=Compiler(7).compile(u);dagfile=BASE.with_suffix('.bin');dag.save(dagfile);ps=list(points(7,320));ptfile=BASE.with_suffix('.txt');ptfile.write_text(f'{len(ps)} 7\n'+'\n'.join(' '.join(map(str,p)) for p in ps)+'\n');out=BASE.with_suffix('.u32');subprocess.run(['/tmp/overnight_lower_dp_engine',str(dagfile),str(ptfile),str(out)],check=True);R=np.fromfile(out,dtype='<u4').reshape(len(ps),len(u)+1).astype(np.int64);basis={};progress=[]
    for i,r in enumerate(R):
        v=reduce(r,basis,PRIME);nz=np.flatnonzero(v[:-1])
        if len(nz):j=int(nz[0]);basis[j]=v*pow(int(v[j]),-1,PRIME)%PRIME
        else:assert v[-1]==0,'target not in full tree span in sampled rows'
        if(i+1)%40==0:progress.append([i+1,len(basis)]);print('rank',progress[-1],flush=True)
    ds=[score_data(x,7) for x in u];results={}
    for mode in('basic','kappa','degree'):
        ff=[features(d,mode) for d in ds];keys=list(ff[0]);F=np.array([[f[k] for f in ff] for k in keys],dtype=np.int64);remainders=np.array([reduce(list(row)+[0],basis,PRIME) for row in F]);ker,rank=nullspace(remainders[:,:-1].T,PRIME);result={'features':len(keys),'constraint_rank':rank,'nullity':len(ker)}
        for v in ker:
            target=int((v@remainders[:,-1])%PRIME)
            if target:
                v=v*pow(-target,-1,PRIME)%PRIME;result['candidate_mod']={k:int(v[i]) for i,k in enumerate(keys) if v[i]};result['target_response_mod']=1;break
        results[mode]=result;print(mode,result,flush=True)
    # The simple N5 score Q, using the original distance form.
    ff=[features(d,'basic') for d in ds]
    Q=np.array([(f['all;d^1;parity^0;orientation^0;one']+f['all;d^1;parity^0;orientation^1;one'])//2+f['both;d^0;parity^0;orientation^0;one']+f['both;d^0;parity^1;orientation^0;one'] for f in ff],dtype=np.int64)
    rem=reduce(list(Q)+[0],basis,PRIME)
    result={'status':'MODULAR_SIGNED_SHUFFLE_QUOTIENT_GATE','arity':7,'prime':PRIME,'units':u,'rows':len(R),'rank_progress':progress,'rank':len(basis),'simple_N5_score_in_sampled_rowspan':bool(np.all(rem[:-1]==0)),'simple_N5_score_response_if_valid':int(-rem[-1]%PRIME),'family':results,'seconds':time.monotonic()-start,'scope':'Modular finite diagnostic, not an exact separator or all-frequency refutation.'}
    BASE.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print('DONE',result['simple_N5_score_in_sampled_rowspan'],result['seconds'],flush=True)
if __name__=='__main__':main()
