"""Exact whole-braid-chamber construction model for the complete pair span.

Each outer preactivation is required to keep a weak sign on every braid
chamber. This is equivalent to same weak sign on every nested pair of
proper Boolean rays. Under this declared restriction, ray equations are
sufficient globally. No coefficient box or point-only refinement is used.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import sys,json,time,hashlib,resource
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_anchor_verify import check
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();mode=sys.argv[1]if len(sys.argv)>1 else'p2';budget=int(sys.argv[2])if len(sys.argv)>2 else 120;control=mode=='control4';N=4 if control else 5;K=1 if control else 3;positive=1 if control else int(mode[1:]);D=[1]*positive+[-1]*(K-positive);pairs=list(combinations(range(N),2));reference=N-1;nc=len(pairs);m=nc+N-1;W=[[z3.Real(f'w{k}_{j}')for j in range(m)]for k in range(K)];R=[z3.Real(f'r{j}')for j in range(m)];resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));z3.set_param('parallel.enable',False);solver=z3.SolverFor('QF_LRA');solver.set(timeout=budget*1000,max_memory=2500)
    def dot(a,b):return z3.Sum([z3.RealVal(x)*v for x,v in zip(a,b)if x])
    relu=lambda x:z3.If(x>=0,x,0)
    subsets=[frozenset(s)for size in range(1,N)for s in combinations(range(N),size)];values={S:[int(i in S and j not in S)for i,j in pairs]+[int(i in S)-int(reference in S)for i in range(N-1)]for S in subsets};g=[{S:dot(values[S],w)for S in subsets}for w in W];nested=[(S,T)for S in subsets for T in subsets if S<T]
    for S in subsets:solver.add(dot(values[S],R)+z3.Sum([d*relu(g[k][S])for k,d in enumerate(D)])==1-int(reference in S))
    for row in g:
        for S,T in nested:solver.add(z3.Or(row[S]<=0,row[T]>=0),z3.Or(row[S]>=0,row[T]<=0))
    if control:
        wc=[0]*m;wc[pairs.index((0,1))]=1;wc[pairs.index((2,3))]=-1;wc[nc+1]=1;rc=[0]*m;rc[pairs.index((2,3))]=1;solver.add(*[W[0][j]==v for j,v in enumerate(wc)],*[R[j]==v for j,v in enumerate(rc)])
    else:
        for w in W:solver.add(w[0]>=0)
        for sign in(1,-1):
            group=[k for k,d in enumerate(D)if d==sign]
            for k,l in zip(group,group[1:]):solver.add(z3.Sum([(j+1)*W[k][j]for j in range(m)])<=z3.Sum([(j+1)*W[l][j]for j in range(m)]))
    prefix='overnight_fixed_complete_braid_'+mode;smt=HERE/(prefix+'.smt2');smt.write_text(solver.to_smt2());print('ENCODED',N,K,'real',(K+1)*m,'nested_pairs',len(nested),'assertions',len(solver.assertions()),'budget',budget,flush=True);answer=solver.check();report={'status':str(answer),'N':N,'core_units':K,'positive_core_outputs':positive,'nested_pairs':len(nested),'real_variables':(K+1)*m,'budget_seconds':budget,'seconds':time.monotonic()-start,'scope':'Complete comparison span; all real coefficients unbounded; each core preactivation has fixed weak sign on each braid chamber. This excludes internal-cancellation constructions from the search. Solver UNSAT remains diagnostic.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest()}
    if answer==z3.sat:
        model=solver.model()
        def value(v):v=model.eval(v,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
        wc=[[value(v)for v in w]for w in W];rc=[value(v)for v in R];A=[[Q(k==i)-Q(k==j)for k in range(N)]for i,j in pairs]+[[Q(k==reference)-Q(k==i)for k in range(N)]for i in range(N-1)]+[[Q(k==reference)*s for k in range(N)]for s in(1,-1)]
        def compile(w,head=False):
            r=w[:nc]+[Q(0)]*(N+1)
            for i in range(N-1):r[pairs.index((i,reference))]+=w[nc+i];r[nc+i]-=w[nc+i]
            if head:r[-2:]=[Q(1),Q(-1)]
            return r
        head=compile(rc,True);net={'N':N,'first_layer':[list(map(str,r))for r in A],'second_layer':[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,compile(w)))for w in wc],'output':['1','-1']+list(map(str,D))};path=HERE/(prefix+'_network.json');path.write_text(json.dumps(net,sort_keys=True,indent=2)+'\n');report['network']=path.name;report['global_check']=check(path);report['status']='GLOBALLY_CERTIFIED_CONSTRUCTION'
    elif answer==z3.unknown:report['reason_unknown']=solver.reason_unknown()
    (HERE/(prefix+'.json')).write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
