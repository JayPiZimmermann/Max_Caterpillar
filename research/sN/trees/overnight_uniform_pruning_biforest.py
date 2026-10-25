"""Bounded N7 diagnostic for the minimal two-rooted-component kernel algebra.

Beyond canonical deficient trees, the only deficient shapes are edge+5-star
and3-path+4-star. Full S7 sums, roots, and all hinge orientations are retained.
"""
from pathlib import Path
from collections import Counter
import itertools,json,math,struct,subprocess,time
import networkx as nx
import numpy as np
from dfs_review_fourier import family
from overnight_uniform_pruning_signed7 import reduce
HERE=Path(__file__).parent;BASE=Path(__file__).with_suffix('');P=1000003

def main():
    start=time.monotonic();units=[]
    for size in(2,3):
        left=family(size+1,'all');right=[u for u in family(8-size,'all')if max(dict(nx.Graph(u['edges']).degree()).values())==6-size]
        for u,v in itertools.product(left,right):
            shift=lambda e:tuple(x+size for x in e);edges=list(u['edges'])+[shift(e)for e in v['edges']];roots=(u['root'],v['root']+size);Q=set(range(size+1,8));cuts=list(u['cuts'])+[(tuple(x+size for x in C),eps)for C,eps in v['cuts']];units.append({'roots':roots,'negative_component':sorted(Q),'edges':edges,'cuts':cuts})
    assert len(units)==96
    permutations=list(itertools.permutations(range(7)));factor_id={};factors=[];starts=[0];states=[]
    for ui,u in enumerate(units):
        counts=Counter()
        for pi in permutations:
            mask=lambda C:sum(1<<pi[x-1]for x in C);a=mask(u['negative_component']);keys=sorted((a,mask(C),int(eps==1))for C,eps in u['cuts']);ids=[]
            for key in keys:
                if key not in factor_id:factor_id[key]=len(factors);factors.append(key)
                ids.append(factor_id[key])
            counts[(a,*ids)]+=1
        for st,c in counts.items():states.append((*st,c))
        starts.append(len(states))
    with BASE.with_suffix('.bin').open('wb')as out:
        out.write(struct.pack('<3I',len(units),len(factors),len(states)));out.write(np.asarray(factors,dtype='<u4').tobytes());out.write(np.asarray(starts,dtype='<u4').tobytes());out.write(np.asarray(states,dtype='<u4').tobytes())
    print('compiled',len(units),len(factors),len(states),time.monotonic()-start,flush=True)
    subprocess.run(['g++','-O3','-std=c++17',str(BASE.with_suffix('.cpp')),'-o','/tmp/overnight_uniform_pruning_biforest'],check=True)
    subprocess.run(['/tmp/overnight_uniform_pruning_biforest',str(BASE.with_suffix('.bin')),str(HERE/'overnight_uniform_pruning_signed7.txt'),str(BASE.with_suffix('.u32'))],check=True)
    old=json.loads((HERE/'overnight_uniform_pruning_signed7.json').read_text());R=np.fromfile(HERE/'overnight_uniform_pruning_signed7.u32',dtype='<u4').reshape(old['rows'],len(old['units'])+1).astype(np.int64);bad=[i for i,u in enumerate(old['units'])if len(nx.max_weight_matching(nx.Graph(u['edges']),maxcardinality=True))<=2];assert len(bad)==258
    B=np.fromfile(BASE.with_suffix('.u32'),dtype='<u4').reshape(old['rows'],96).astype(np.int64);M=np.concatenate([R[:,bad],B,R[:,-1:]],axis=1);basis={};progress=[]
    for i,r in enumerate(M):
        v=reduce(r,basis,P);nz=np.flatnonzero(v)
        if len(nz):j=int(nz[0]);basis[j]=v*pow(int(v[j]),-1,P)%P
        if(i+1)%40==0:progress.append([i+1,len(basis),int(M.shape[1]-1 in basis)]);print('rank',progress[-1],flush=True)
    result={'status':'MODULAR_TWO_ROOT_MATCHING_DEFICIENCY_GATE','arity':7,'prime':P,'new_units':units,'canonical_deficient_columns':258,'new_columns':96,'rows':len(M),'rank_progress':progress,'augmented_rank':len(basis),'target_is_independent':bool(M.shape[1]-1 in basis),'seconds':time.monotonic()-start,'scope':'Finite-field diagnostic for two tree components joined by a pure root-difference head; not a canonical all-tree theorem or exact rational certificate.'};BASE.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print('DONE',result['target_is_independent'],result['seconds'],flush=True)
if __name__=='__main__':main()
