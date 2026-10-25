"""Unbounded real physical9,6 synthesis, without a prescribed linear head.

Both translation-tail identities and finite input/output identities are
necessary. Only the independent720-cone checker can certify a construction.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json,hashlib,sys,time,resource,math
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_physical_counterexample import find
from overnight_fixed_exact_counterexample import evaluate
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();orientation=int(sys.argv[1]);positive=int(sys.argv[2]);budget=int(sys.argv[3])if len(sys.argv)>3 else 180;step=int(sys.argv[4])if len(sys.argv)>4 else 45;control=sys.argv[5]if len(sys.argv)>5 else None;resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));z3.set_param('parallel.enable',False)
    inventory=json.loads((HERE/'overnight_fixed_cycle9_orientations.json').read_text());edges=[r['edges']for r in inventory['results']if r['witness']is None][orientation];A=[[Q(k==i)-Q(k==j)for k in range(5)]for i,j in edges]+[[Q(i==j)*s for i in range(5)]for j in(0,2)for s in(1,-1)];D=[Q(1)]*positive+[Q(-1)]*(6-positive);K=6;m=9;N=5;cn=None
    if control:cn=json.loads((HERE/control).read_text());A=[list(map(Q,r))for r in cn['first_layer']];D=list(map(Q,cn['output']));K=len(D);m=len(A)
    W=[[z3.Real(f'w{k}_{j}')for j in range(m)]for k in range(K)];solver=z3.SolverFor('QF_LRA');solver.set(max_memory=2500)
    def rat(v):v=Q(v);return z3.RealVal(f'{v.numerator}/{v.denominator}')
    def dot(v,w):return z3.Sum([rat(x)*y for x,y in zip(v,w)if x])
    relu=lambda v:z3.If(v>=0,v,0)
    absolute=lambda v:z3.If(v>=0,v,-v)
    def add_point(x):
        phi=[max(sum(a*t for a,t in zip(row,x)),Q(0))for row in A];solver.add(z3.Sum([rat(d)*relu(dot(phi,w))for d,w in zip(D,W)])==rat(max(x)))
    # Same-sign neuron permutation only. A global preactivation flip would
    # require a free shallow remainder and is NOT a valid physical symmetry.
    if cn:
        for k,row in enumerate(cn['second_layer']):solver.add(*[W[k][j]==rat(v)for j,v in enumerate(row)])
    else:
        for sign in(1,-1):
            group=[k for k,d in enumerate(D)if d==sign]
            for k,l in zip(group,group[1:]):solver.add(z3.Sum([(2**j)*W[k][j]for j in range(m)])<=z3.Sum([(2**j)*W[l][j]for j in range(m)]))
    sets=[frozenset(c)for size in range(1,N+1)for c in combinations(range(N),size)];localities=[(U,o)for U in sets if len(U)==3 for o in range(N)if o not in U]+[(U,None)for U in sets if len(U)in(4,5)]
    for S in sets:
        x=[Q(i in S)for i in range(N)];add_point(x);add_point([-v for v in x])
    for tail in(1,-1):
        slopes=[sum(row)for row in A];base=[max(tail*s,Q(0))for s in slopes];atbase=[dot(base,w)for w in W];solver.add(z3.Sum([rat(d)*relu(v)for d,v in zip(D,atbase)])==tail)
        values={S:[(sum(row[i]for i in S)if tail*s>0 else Q(0))if s else max(sum(row[i]for i in S),Q(0))for row,s in zip(A,slopes)]for S in sets};g=[{S:dot(values[S],w)for S in sets}for w in W]
        for S in sets:solver.add(z3.Sum([rat(d)*z3.If(atbase[k]>0,g[k][S],z3.If(atbase[k]<0,0,relu(g[k][S])))for k,d in enumerate(D)])==1)
        for U,o in localities:
            terms=[]
            for k,d in enumerate(D):
                active=atbase[k]==0
                if len(U)<N:active=z3.And(active,g[k][U]==0)
                if o is not None:active=z3.And(active,g[k][U|{o}]==0)
                mixed=z3.Sum([((-1)**(len(U)-len(S)))*absolute(g[k][S])for S in sets if S<U]);terms.append(z3.If(active,rat(d)*mixed,0))
            solver.add(z3.Sum(terms)==2*((-1)**(len(U)+1)))
    prefix=f'overnight_fixed_cycle9_physical_o{orientation}_p{positive}'+('_control'if control else'');steps=[];final=None;seen=set();status='ITERATION_LIMIT';logpath=HERE/(prefix+'_steps.jsonl');print('START',prefix,'budget',budget,'step',step,'real',K*m,'assertions',len(solver.assertions()),flush=True)
    with logpath.open('w')as log:
        for it in range(24):
            remaining=budget-(time.monotonic()-start)
            if remaining<=0:status='CAMPAIGN_BUDGET';break
            solver.set(timeout=int(1000*min(step,remaining)));t=time.monotonic();answer=solver.check();r={'iteration':it,'solver_status':str(answer),'solve_seconds':time.monotonic()-t}
            if answer!=z3.sat:
                status='UNSAT_NECESSARY_SYSTEM'if answer==z3.unsat else'SOLVER_UNKNOWN';r['reason']=solver.reason_unknown()if answer==z3.unknown else None;steps.append(r);log.write(json.dumps(r)+'\n');log.flush();print(r,flush=True);break
            model=solver.model()
            def value(v):v=model.eval(v,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
            candidate={'N':N,'first_layer':[list(map(str,row))for row in A],'second_layer':[[str(value(v))for v in row]for row in W],'output':list(map(str,D))};path=HERE/(prefix+f'_candidate_{it:02}.json');path.write_text(json.dumps(candidate,sort_keys=True,indent=2)+'\n');r['candidate']=path.name;r['candidate_sha256']=hashlib.sha256(path.read_bytes()).hexdigest();counter,receipt=find(path)
            if receipt:
                status='GLOBALLY_CERTIFIED_CONSTRUCTION';final={'network':path.name,'receipt':receipt};r['global_check']=receipt;steps.append(r);log.write(json.dumps(r)+'\n');log.flush();print('CERTIFIED',receipt,flush=True);break
            point=list(map(Q,counter['point']));den=math.lcm(*(v.denominator for v in point));ints=[int(v*den)for v in point];div=math.gcd(*ints);point=tuple(v//div for v in ints);assert point not in seen;seen.add(point);actual=evaluate(candidate,point);assert actual!=max(point);add_point(point);r['counterexample']={'point':point,'network_value':str(actual),'target_value':str(max(point)),'cone':counter['augmented_braid_cone']};steps.append(r);log.write(json.dumps(r)+'\n');log.flush();print('CUT',it,point,'error',str(actual-max(point)),flush=True)
    smt=HERE/(prefix+'.smt2');smt.write_text(solver.to_smt2());report={'status':status,'orientation':orientation,'positive_outputs':positive,'physical_widths':[m,K],'prescribed_linear_head':False,'coefficients':'all real, unbounded','campaign_budget_seconds':budget,'per_step_budget_seconds':step,'steps':len(steps),'counterexamples':len(seen),'construction':final,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'steps_sha256':hashlib.sha256(logpath.read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest(),'scope':'Necessary physical-network and both translation-tail identities; only a successful independent global720-cone check is a construction. Solver UNSAT is diagnostic pending independent proof.'};(HERE/(prefix+'.json')).write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
