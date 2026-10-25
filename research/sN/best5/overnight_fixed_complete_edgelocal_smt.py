"""Exact four-tie-zero complete-comparison construction model.

Edge coefficients b_k sum to zero and g_k=−sum_e b_ke max(x_i,x_j).
Every edge is assigned a zero neuron (closed disjunction). Ray equations
force the remainder coefficients; whole-cone pair cancellation makes the
candidate globally exact. Genuine three-way cancellation is excluded.
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
    start=time.monotonic();mode=sys.argv[1]if len(sys.argv)>1 else'p2';budget=int(sys.argv[2])if len(sys.argv)>2 else 180;control=mode=='control10';K=4 if control else 3;positive=3 if control else int(mode[1:]);D=[1]*positive+[-1]*(K-positive);N=5;edges=list(combinations(range(N),2));B=[[z3.Real(f'b{k}_{e}')for e in range(10)]for k in range(K)];resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));z3.set_param('parallel.enable',False);solver=z3.SolverFor('QF_LRA');solver.set(timeout=budget*1000,max_memory=2500);relu=lambda x:z3.If(x>=0,x,0);absolute=lambda x:z3.If(x>=0,x,-x);subsets=[frozenset(s)for size in range(1,N)for s in combinations(range(N),size)];full=frozenset(range(N));contained=lambda T:[e for e,(i,j)in enumerate(edges)if i in T and j in T];g=[{S:z3.Sum([row[e]for e in contained(full-S)])for S in subsets}for row in B];R=[z3.Sum([d*relu(B[k][e])for k,d in enumerate(D)])for e in range(10)]
    for row in B:solver.add(z3.Sum(row)==0)
    solver.add(z3.Sum(R)==1)
    for e in range(10):solver.add(z3.Or([B[k][e]==0 for k in range(K)]))
    for size in(3,4):
        for T in combinations(range(N),size):
            es=contained(T);solver.add(z3.Sum([R[e]for e in es])==z3.Sum([d*relu(z3.Sum([B[k][e]for e in es]))for k,d in enumerate(D)]))
    localities=[(U,o)for U in subsets if len(U)==3 for o in range(N)if o not in U]+[(U,None)for U in subsets+[full]if len(U)in(4,5)]
    for U,o in localities:
        terms=[]
        for k,d in enumerate(D):
            active=z3.BoolVal(True)if len(U)>=4 else g[k][U]==0
            mixed=z3.Sum([((-1)**(len(U)-len(S)))*absolute(g[k][S])for S in subsets if S<U]);terms.append(z3.If(active,d*mixed,0))
        solver.add(z3.Sum(terms)==2*((-1)**(len(U)+1)))
    if control:
        pp,rr,cc=convert_network(HERE/'netB_10_6.json');assert pp==edges and[d for d,w in cc]==D
        for k,(d,w)in enumerate(cc):
            b=[-v for v in w[:10]];assert sum(b)==0
            for e,v in enumerate(b):solver.add(B[k][e]==z3.RealVal(f'{v.numerator}/{v.denominator}'))
    else:
        for row in B:solver.add(row[0]>=0)
        for sign in(1,-1):
            ids=[k for k,d in enumerate(D)if d==sign]
            for i,j in zip(ids,ids[1:]):solver.add(z3.Sum([(e+1)*B[i][e]for e in range(10)])<=z3.Sum([(e+1)*B[j][e]for e in range(10)]))
    prefix='overnight_fixed_complete_edgelocal_'+mode;smt=HERE/(prefix+'.smt2');smt.write_text(solver.to_smt2());print('ENCODED',mode,'real',10*K,'assertions',len(solver.assertions()),'budget',budget,flush=True);answer=solver.check();report={'status':str(answer),'core_units':K,'positive_outputs':positive,'real_variables':10*K,'budget_seconds':budget,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest(),'scope':'All four-label tie values zero, arbitrary real edge coefficients, closed edge-zero cover, exact Boolean-ray and generic-tie necessary equations. No whole-cone constraint. Only an independent global check can certify a construction; UNSAT remains a solver diagnostic.'}
    if answer==z3.sat:
        model=solver.model()
        def value(v):v=model.eval(v,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
        b=[[value(v)for v in row]for row in B];r=[value(v)for v in R];assert all(sum(row)==0 for row in b)and sum(r)==1
        def canonical(coeff):return coeff+[sum(coeff[e]for e,(i,j)in enumerate(edges)if j==k)for k in range(4)]
        rc=canonical(r);wc=[canonical([-v for v in row])for row in b];A=[[Q(k==i)-Q(k==j)for k in range(N)]for i,j in edges]+[[Q(k==4)-Q(k==i)for k in range(N)]for i in range(4)]+[[Q(k==4)*s for k in range(N)]for s in(1,-1)]
        def compile(w,head=False):
            out=w[:10]+[Q(0)]*6
            for i in range(4):out[edges.index((i,4))]+=w[10+i];out[10+i]-=w[10+i]
            if head:out[-2:]=[Q(1),Q(-1)]
            return out
        head=compile(rc,True);net={'N':N,'first_layer':[list(map(str,row))for row in A],'second_layer':[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,compile(w)))for w in wc],'output':['1','-1']+list(map(str,D))};path=HERE/(prefix+'_network.json');path.write_text(json.dumps(net,sort_keys=True,indent=2)+'\n');report['network']=path.name;report['edge_coefficients']=[list(map(str,row))for row in b]
        try:report['global_check']=check(path);report['status']='GLOBALLY_CERTIFIED_CONSTRUCTION'
        except AssertionError as exc:report['status']='EXACT_NECESSARY_SYSTEM_SURVIVOR';report['global_failure']=str(exc)
    elif answer==z3.unknown:report['reason_unknown']=solver.reason_unknown()
    (HERE/(prefix+'.json')).write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
