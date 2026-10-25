"""Complete-comparison synthesis allowing exact pairwise interior cancellation.

On each braid chamber every crossing outer form must pair with an opposite
output sign, with equal or opposite preactivation. The remaining units have
a weak fixed sign. Three-way cancellation is excluded from this constructive
gate. With these whole-cone conditions, Boolean-ray equations prove equality.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations,permutations
import sys,json,time,hashlib,resource
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_anchor_verify import check
from overnight_fixed_complete_coordinates import convert_network
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();mode=sys.argv[1]if len(sys.argv)>1 else'p2';budget=int(sys.argv[2])if len(sys.argv)>2 else 120;control=mode=='control10';N=5;K=4 if control else 3;positive=3 if control else 2;D=[1]*positive+[-1]*(K-positive);pairs=list(combinations(range(N),2));reference=N-1;nc=len(pairs);m=nc+N-1;W=[[z3.Real(f'w{k}_{j}')for j in range(m)]for k in range(K)];R=[z3.Real(f'r{j}')for j in range(m)];resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));z3.set_param('parallel.enable',False);solver=z3.SolverFor('QF_LRA');solver.set(timeout=budget*1000,max_memory=2500)
    def dot(a,b):return z3.Sum([z3.RealVal(x)*v for x,v in zip(a,b)if x])
    relu=lambda x:z3.If(x>=0,x,0)
    subsets=[frozenset(s)for size in range(1,N)for s in combinations(range(N),size)];values={S:[int(i in S and j not in S)for i,j in pairs]+[int(i in S)-int(reference in S)for i in range(N-1)]for S in subsets};g=[{S:dot(values[S],w)for S in subsets}for w in W];nested=[(S,T)for S in subsets for T in subsets if S<T]
    for S in subsets:solver.add(dot(values[S],R)+z3.Sum([d*relu(g[k][S])for k,d in enumerate(D)])==1-int(reference in S))
    full=frozenset(range(N));localities=[(U,o)for U in subsets if len(U)==3 for o in range(N)if o not in U]+[(U,None)for U in subsets+[full]if len(U)in(4,5)]
    absolute=lambda x:z3.If(x>=0,x,-x)
    for U,o in localities:
        terms=[]
        for k,d in enumerate(D):
            active=z3.BoolVal(True)if len(U)==N else g[k][U]==0
            if o is not None:active=z3.And(active,g[k][U|{o}]==0)
            mixed=z3.Sum([((-1)**(len(U)-len(S)))*absolute(g[k][S])for S in subsets if S<U]);terms.append(z3.If(active,d*mixed,0))
        solver.add(z3.Sum(terms)==2*((-1)**(len(U)+1)))
    for p in permutations(range(N)):
        chain=[frozenset(p[:t])for t in range(1,N)]
        def fixed(k):return z3.Or(z3.And([g[k][S]>=0 for S in chain]),z3.And([g[k][S]<=0 for S in chain]))
        options=[z3.And([fixed(k)for k in range(K)])]
        # For K3 a single cancelling pair is exhaustive for the declared
        # restriction. The K4 control can also contain two disjoint pairs.
        choices=[(i,j)for i in range(K)for j in range(i+1,K)if D[i]!=D[j]]
        for i,j in choices:
            for eps in(1,-1):options.append(z3.And([g[i][S]==eps*g[j][S]for S in chain]+[fixed(k)for k in range(K)if k not in(i,j)]))
        if K==4:
            for (i,j),(k,l)in combinations(choices,2):
                if len({i,j,k,l})!=4:continue
                for e in(1,-1):
                    for f in(1,-1):options.append(z3.And([g[i][S]==e*g[j][S]for S in chain]+[g[k][S]==f*g[l][S]for S in chain]))
        solver.add(z3.Or(options))
    if control:
        net=json.loads((HERE/'netB_10_6.json').read_text());physical=[list(map(Q,r))for r in net['first_layer']];weights=[list(map(Q,r))for r in net['second_layer']];outputs=list(map(Q,net['output']))
        def convert(w,head=False):
            out=[Q(0)]*nc;linear=[Q(0)]*N;carriers={}
            for row,c in zip(physical,w):
                nz=[i for i,v in enumerate(row)if v]
                if len(nz)==1:carriers[nz[0],int(row[nz[0]])]=c;continue
                i=next(i for i,v in enumerate(row)if v>0);j=next(i for i,v in enumerate(row)if v<0);assert row[i]==1 and row[j]==-1
                out[pairs.index(tuple(sorted((i,j))))]+=c
                if i>j:linear[i]+=c;linear[j]-=c
            for i in{j for j,sgn in carriers}:assert carriers[i,1]==-carriers[i,-1];linear[i]+=carriers[i,1]
            if head:linear[reference]-=1
            assert sum(linear)==0
            return out+linear[:-1]
        core=[(int(d>0)*2-1,[abs(d)*v for v in convert(w)])for d,w in zip(outputs[2:],weights[2:])];core.sort(key=lambda z:-z[0]);assert[d for d,w in core]==D;rc=convert(weights[0],True)
        def rat(v):return z3.RealVal(f'{v.numerator}/{v.denominator}')
        for k,(_,w)in enumerate(core):solver.add(*[W[k][j]==rat(v)for j,v in enumerate(w)])
        solver.add(*[R[j]==rat(v)for j,v in enumerate(rc)])
    else:
        assert mode.startswith('merge');merge_index=int(mode[5:]);merge_pair=list(combinations(range(3),2))[merge_index];remaining=next(i for i in range(3)if i not in merge_pair);oldpairs,oldR,oldcore=convert_network(HERE/'netB_10_6.json',reference);assert oldpairs==pairs and[d for d,w in oldcore]==[1,1,1,-1];oldW=[w for d,w in oldcore]
        oldvalues=[{S:sum(Q(a)*b for a,b in zip(values[S],w))for S in subsets}for w in oldW];incidence_counts={'pair_merged':0,'pair_single':0,'all_fixed':0,'merged_sign_free':0}
        for p in permutations(range(N)):
            chain=[frozenset(p[:t])for t in range(1,N)];ov=[[row[S]for S in chain]for row in oldvalues];mixed=[k for k,row in enumerate(ov)if min(row)<0<max(row)]
            def stable(k,sample):
                if min(sample)>=0 and max(sample)>0:solver.add(*[g[k][S]>=0 for S in chain])
                elif max(sample)<=0 and min(sample)<0:solver.add(*[g[k][S]<=0 for S in chain])
                else:
                    solver.add(z3.Or(z3.And([g[k][S]>=0 for S in chain]),z3.And([g[k][S]<=0 for S in chain])));incidence_counts['merged_sign_free']+=1
            merged=[sum(ov[i][j]for i in merge_pair)for j in range(N-1)]
            if not mixed:stable(0,merged);stable(1,ov[remaining]);stable(2,ov[3]);incidence_counts['all_fixed']+=1;continue
            assert len(mixed)==2 and 3 in mixed;partner=next(k for k in mixed if k!=3);eps=1 if ov[partner]==ov[3]else-1;assert ov[partner]==[eps*v for v in ov[3]]
            if partner in merge_pair:newpartner=0;stable(1,ov[remaining]);incidence_counts['pair_merged']+=1
            else:newpartner=1;stable(0,merged);incidence_counts['pair_single']+=1
            solver.add(*[g[newpartner][S]==eps*g[2][S]for S in chain])
    prefix='overnight_fixed_complete_incidence_'+mode;smt=HERE/(prefix+'.smt2');smt.write_text(solver.to_smt2());print('ENCODED',N,K,'real',(K+1)*m,'nested_pairs',len(nested),'assertions',len(solver.assertions()),'budget',budget,flush=True);answer=solver.check();report={'status':str(answer),'N':N,'core_units':K,'positive_core_outputs':positive,'nested_pairs':len(nested),'generic_tie_equations':len(localities),'real_variables':(K+1)*m,'budget_seconds':budget,'seconds':time.monotonic()-start,'scope':'Complete comparison span, unbounded real coefficients. Three positive core neurons from the known four-core construction are merged in one declared pair; exact whole-cone cancellation assignments and stable signs are retained while every coefficient changes. Only globally checked SAT is a construction; UNSAT excludes this incidence family only.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest()}
    if not control:report['merged_positive_pair']=merge_pair;report['incidence_counts']=incidence_counts
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
