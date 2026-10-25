"""Bounded exact local-relation test of the existing 288-feature score family.

No new features. Modular elimination only selects independent exact integer
constraints. Any exclusion is subsequently solved and checked over Q.
"""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as Q
import itertools,json,sys,time
import numpy as np
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq_mat,ctx
from overnight_uniform_pruning_candidate_target import root_counts
from overnight_uniform_pruning_signed_family import features,score_data
from overnight_uniform_q9_local_gate import rewires
from dfs_review_fourier import family

HERE=Path(__file__).parent;BASE=Path(__file__).with_suffix('');P=1000003
KEYS=[f'{ep};d^{pw};parity^{par};orientation^{sgn};{mul}'for ep,pw,par,sgn,mul in itertools.product(('all','both','one','none'),range(3),range(2),range(2),('one','k_sum','k_prod','k_diff2','deg_sum','deg_prod'))]

@lru_cache(None)
def structure(undirected):
    V=sorted({v for e in undirected for v in e});T={v:set()for v in V}
    for v,w in undirected:T[v].add(w);T[w].add(v)
    I=root_counts(T);dist=np.zeros((len(V),len(V)),dtype=np.int64)
    for i,v in enumerate(V):
        d={v:0};todo=[v]
        for w in todo:
            for j in T[w]:
                if j not in d:d[j]=d[w]+1;todo.append(j)
        dist[i]=[d[w]for w in V]
    return V,T,np.array([I[v]for v in V],dtype=np.int64),dist

@lru_cache(None)
def feature_tuple(root,edges):
    V,T,I,dist=structure(tuple(sorted(tuple(sorted(e))for e in edges)))
    if not np.any(I):return (0,)*288
    E=set(edges);parent={root:None};todo=[root];A={root};eps=1
    for v in todo:
        for w in T[v]:
            if w!=parent[v]:
                parent[w]=v;todo.append(w);sgn=1 if(w,v)in E else -1;eps*=sgn
                if v in A and sgn==1:A.add(w)
    k=np.array([int(v==root)+sum(a==v for a,b in E)for v in V],dtype=np.int64)
    deg=np.array([len(T[v])for v in V],dtype=np.int64)
    poly=np.stack((np.ones_like(dist),k[:,None]+k[None,:],k[:,None]*k[None,:],(k[:,None]-k[None,:])**2,deg[:,None]+deg[None,:],deg[:,None]*deg[None,:]),axis=-1).reshape(-1,6)
    isin=np.array([int(v in A)for v in V]);inside=isin[:,None]+isin[None,:];weight=I[:,None]*I[None,:];out=[]
    for mask in(np.ones_like(dist),inside==2,inside==1,inside==0):
        for pw in range(3):
            for par in range(2):
                row=(weight*mask*(dist**pw)*((-1)**(par*dist))).reshape(-1)@poly
                out.extend(map(int,row));out.extend(map(int,eps*row))
    return tuple(out)

def vec(u):return np.array(feature_tuple(u['root'],tuple(sorted(map(tuple,u['edges'])))),dtype=np.int64)

def target(N):
    out=np.zeros(288,dtype=np.int64)
    for mask in range(1,1<<(N-2)):
        S={j for j in range(1,N-1)if mask>>(j-1)&1};E=[]
        for j in range(1,N-1):E.append((max([0]+[i for i in S if i<j])+1,j+1))
        out+=(-1)**(N+len(S))*vec({'root':max(S)+1,'edges':E})
    return out

def reduce(row,basis):
    row=np.array(row,dtype=np.int64)%P
    for j,b in sorted(basis.items()):
        if row[j]:row=(row-row[j]*b)%P
    return row

def add(row,basis):
    r=reduce(row,basis);nz=np.flatnonzero(r)
    if not len(nz):return False
    j=int(nz[0]);basis[j]=r*pow(int(r[j]),-1,P)%P;return True

def exact_combination(rows,t):
    A=fmpq_mat([[int(rows[j][i])for j in range(len(rows))]+[int(t[i])]for i in range(288)]);R,rank=A.rref();r=len(rows)
    if rank!=r:return None
    assert all(R[i,j]==int(i==j)for i in range(r)for j in range(r))
    w=[Q(str(R[j,r]))for j in range(r)]
    assert all(sum(w[j]*int(rows[j][i])for j in range(r))==int(t[i])for i in range(288))
    return list(map(str,w))

def main():
    ctx.threads=1;start=time.monotonic();prior=BASE.with_suffix('.json');D=json.loads(prior.read_text())if prior.exists()else None
    units={5:family(5,'all'),7:family(7,'all'),9:json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text())['units']}
    # Exact agreement with the old feature alphabet on the entire N5 family.
    for u in units[5]:
        old=features(score_data(u,5),'degree');assert list(old)==KEYS;assert tuple(old.values())==tuple(vec(u))
    targets={n:target(n)for n in(5,7,9)};rows=[];witnesses=[];basis={};progress=[];certificates={}
    if D:
        rows=D['independent_constraint_rows'];witnesses=D['constraint_witnesses'];progress=D['progress'];certificates=D.get('exact_target_combinations',{})
        for row in rows:assert add(row,basis)
    done=D['processed']if D else 0;processed=0
    def save(status):
        out={'status':status,'features':KEYS,'feature_count':288,'processed':processed,'independent_constraint_rows':rows,'constraint_witnesses':witnesses,'rank_mod':len(basis),'targets':{str(n):list(map(int,t))for n,t in targets.items()},'exact_target_combinations':certificates,'progress':progress,'seconds_this_phase':time.monotonic()-start,'scope':'All constraints are exact six-term grafting rational identities. A modular basis only selects rows; exact target combinations are independently checked over Q. No enlarged feature alphabet.'};prior.write_text(json.dumps(out,indent=2)+'\n')
    for N,us in units.items():
        for j,U in enumerate(us):
            E=list(map(tuple,U['edges']));V,T,_,_=structure(tuple(sorted(tuple(sorted(e))for e in E)));root=U['root'];parent={root:None};todo=[root]
            for r in todo:
                for v in T[r]:
                    if v!=parent[r]:parent[v]=r;todo.append(v)
            for r in todo:
                for v,w in itertools.combinations(sorted(v for v in T[r]if v!=parent[r]),2):
                    processed+=1
                    if processed<=done:continue
                    terms=rewires({'root':root,'edges':E},r,v,w);row=sum((c*vec(u)for c,u in terms),np.zeros(288,dtype=np.int64))
                    if add(row,basis):
                        rows.append(list(map(int,row)));witnesses.append({'arity':N,'raw_index':j,'source':{'root':root,'edges':E},'junction':r,'children':[v,w]})
                        for n,t in targets.items():
                            if str(n)not in certificates and not np.any(reduce(t,basis)):
                                solution=exact_combination(rows,t)
                                if solution is not None:certificates[str(n)]={'constraint_count':len(rows),'weights':solution};print('EXACT TARGET ZERO',n,'rank',len(rows),'processed',processed,flush=True)
                        if len(rows)%10==0:
                            progress.append({'processed':processed,'arity':N,'rank':len(rows),'seconds':time.monotonic()-start});print(progress[-1],flush=True);save('IN_PROGRESS')
                    if len(certificates)==3:save('EXACT_ALL_THREE_TARGETS_FORCED_ZERO');return
                    if time.monotonic()-start>105:save('BOUNDED_PHASE_COMPLETE');return
    save('ALL_LOCAL_IDENTITIES_THROUGH_N9_EXHAUSTED');print('EXHAUSTED',processed,'rank',len(rows),'certificates',list(certificates),flush=True)

if __name__=='__main__':main()
