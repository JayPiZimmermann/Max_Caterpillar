"""Joint four-core proposal on C5 with arbitrary signed-group cancellation.

A linear-real necessary relaxation: each spurious group has zero signed
sum of oriented gradients. Common orientation and collinearity are not
assumed by the solver; every SAT model is globally checked, and failures
record the exact missing quadratic constraints. No coefficient bounds.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,combinations,product
import json,sys,time,hashlib,resource,math
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_anchor_verify import check as globalcheck
from overnight_fixed_exact_counterexample import find as global_or_counterexample, evaluate
HERE=Path(__file__).resolve().parent


def main():
    orientation=int(sys.argv[1]);mode=sys.argv[2]if len(sys.argv)>2 else 'p3';budget=int(sys.argv[3])if len(sys.argv)>3 else 120;start=time.monotonic();resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));z3.set_param('parallel.enable',False);N=5;inventory=json.loads((HERE/'overnight_fixed_cycle9_orientations.json').read_text());survivors=[r for r in inventory['results']if r['witness']is None];edges=survivors[orientation]['edges'];comparison=[[Q(k==i)-Q(k==j)for k in range(5)]for i,j in edges];lin=[Q(i==2)-Q(i==0)for i in range(5)];A=comparison+[lin];m=6;reference=0;physical=comparison+[[Q(i==j)*s for i in range(5)]for j in(0,2)for s in(1,-1)];net={'N':5,'first_layer':[[str(x)for x in row]for row in physical]};cells={}
    for p in permutations(range(N)):
        rank={v:i for i,v in enumerate(p)};act=[row if rank[next(i for i,x in enumerate(row)if x>0)]<rank[next(i for i,x in enumerate(row)if x<0)]else[Q(0)]*N for row in comparison]+[lin];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'sets':set(),'tops':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,N));cell['tops'].add(p[0])
    for cell in cells.values():assert len(cell['tops'])<=2
    signs=[1]*int(mode[1:])+[-1]*(4-int(mode[1:]));constants=None
    K=len(signs);positive=[k for k,d in enumerate(signs)if d>0];negative=[k for k,d in enumerate(signs)if d<0];W=[[z3.Real(f'w_{k}_{j}')for j in range(m)]for k in range(K)];R=[z3.Real(f'r_{j}')for j in range(m)];solver=z3.SolverFor('QF_LRA');solver.set(timeout=budget*1000);solver.set(max_memory=2500)
    def rat(v):v=Q(v);return z3.RealVal(f'{v.numerator}/{v.denominator}')
    def dot(a,b):return z3.Sum([rat(x)*y for x,y in zip(a,b)if x])
    if constants is not None:
        for k,(d,w)in enumerate(constants):solver.add(*[W[k][j]==rat(w[j])for j in range(m)])
        solver.add(*[R[j]==rat(Rconst[j])for j in range(m)])
    for row in W:solver.add(row[0]>=0)
    for group in(positive,negative):
        for k,l in zip(group,group[1:]):solver.add(z3.Sum([(2**j)*W[k][j]for j in range(m)])<=z3.Sum([(2**j)*W[l][j]for j in range(m)]))
    # Exact necessary equations, independently of the cell-incidence relaxation.
    sets=[frozenset(c)for size in range(1,N+1)for c in combinations(range(N),size)]
    values={S:[max(sum(row[i]for i in S),Q(0))for row in comparison]+[sum(lin[i]for i in S)]for S in sets}
    evaluations=[{S:dot(values[S],row)for S in sets}for row in W]
    relu=lambda x:z3.If(x>=0,x,0)
    absolute=lambda x:z3.If(x>=0,x,-x)
    for S in sets:
        solver.add(dot(values[S],R)+z3.Sum([d*relu(evaluations[k][S])for k,d in enumerate(signs)])==rat(1-int(reference in S)))
    localities=[(U,o)for U in sets if len(U)==3 for o in range(N)if o not in U]+[(U,None)for U in sets if len(U)in(4,5)]
    for U,o in localities:
        terms=[]
        for k,d in enumerate(signs):
            active=z3.BoolVal(True)if len(U)==N else(evaluations[k][U]==0)
            if o is not None:active=z3.And(active,evaluations[k][U|{o}]==0)
            mixed=z3.Sum([((-1)**(len(U)-len(S)))*absolute(evaluations[k][S])for S in sets if S<U])
            terms.append(z3.If(active,d*mixed,0))
        solver.add(z3.Sum(terms)==rat(2*((-1)**(len(U)+1))))
    bools=0;debug=[]
    step_budget=int(sys.argv[4])if len(sys.argv)>4 else 30
    prefix=f'overnight_fixed_cycle9_cegis_o{orientation}_{mode}'
    logpath=HERE/(prefix+'_steps.jsonl');steps=[];seen=set();final=None;status='ITERATION_LIMIT';max_steps=32
    print('START',orientation,mode,'campaign',budget,'step',step_budget,'iterations',max_steps,'assertions',len(solver.assertions()),flush=True)
    with logpath.open('w')as log:
      for iteration in range(max_steps):
        remaining=budget-(time.monotonic()-start)
        if remaining<=0:status='CAMPAIGN_BUDGET';break
        solver.set(timeout=int(1000*min(step_budget,remaining)));step_start=time.monotonic();answer=solver.check();record={'iteration':iteration,'solver_status':str(answer),'solve_seconds':time.monotonic()-step_start}
        if answer!=z3.sat:
            status='UNSAT_GENUINE_NECESSARY_SYSTEM'if answer==z3.unsat else'SOLVER_UNKNOWN'
            if answer==z3.unknown:record['reason_unknown']=solver.reason_unknown()
            steps.append(record);log.write(json.dumps(record,separators=(',',':'))+'\n');log.flush();print(record,flush=True);break
        model=solver.model()
        def value(expr):v=model.eval(expr,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
        wc=[[value(x)for x in row]for row in W];rc=[value(x)for x in R];head=rc[:5]+[1-rc[5],-1+rc[5],rc[5],-rc[5]];physical_core=[row[:5]+[-row[5],row[5],row[5],-row[5]]for row in wc];candidate={'N':N,'first_layer':net['first_layer'],'second_layer':[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,row))for row in physical_core],'output':['1','-1']+list(map(str,signs))};path=HERE/(prefix+f'_candidate_{iteration:02}.json');path.write_text(json.dumps(candidate,sort_keys=True,indent=2)+'\n');record['candidate']=path.name;record['candidate_sha256']=hashlib.sha256(path.read_bytes()).hexdigest();counter,receipt=global_or_counterexample(path)
        if receipt is not None:
            record['global_check']=receipt;steps.append(record);log.write(json.dumps(record,separators=(',',':'))+'\n');log.flush();status='GLOBALLY_CERTIFIED_CONSTRUCTION';final={'network':path.name,'global_check':receipt};print('CERTIFIED',final,flush=True);break
        x=list(map(Q,counter['point']));x=[v-x[0]for v in x];den=math.lcm(*(v.denominator for v in x));integers=[int(v*den)for v in x];divisor=math.gcd(*integers);assert divisor>0;point=tuple(v//divisor for v in integers);assert point not in seen;seen.add(point);actual=evaluate(candidate,list(map(Q,point)));target=max(point);assert actual!=target;z=[max(Q(point[i]-point[j]),Q(0))for i,j in edges]+[Q(point[2]-point[0])];constraint=dot(z,R)+z3.Sum([d*relu(dot(z,W[k]))for k,d in enumerate(signs)])==rat(target-point[0]);solver.add(constraint);record['counterexample']={'point':point,'network_value':str(actual),'target_value':str(target),'braid_cone':counter['braid_cone'],'source':counter['source']};record['assertions_after_cut']=len(solver.assertions());steps.append(record);log.write(json.dumps(record,separators=(',',':'))+'\n');log.flush();print('CUT',iteration,point,'error',str(actual-target),'seconds',time.monotonic()-start,flush=True)
    smt=HERE/(prefix+'.smt2');smt.write_text(solver.to_smt2());report={'status':status,'orientation_index':orientation,'comparison_edges':edges,'positive_units':len(positive),'negative_units':len(negative),'campaign_budget_seconds':budget,'per_iteration_budget_seconds':step_budget,'max_iterations':max_steps,'iterations':len(steps),'exact_counterexamples':len(seen),'seconds':time.monotonic()-start,'construction':final,'z3_version':z3.get_version_string(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'steps_sha256':hashlib.sha256(logpath.read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest(),'scope':'Unbounded real four-core C5 synthesis. Every cut is an exact rational input/output counterexample; only a complete independent global check certifies a construction. UNSAT is a solver diagnostic pending an independent proof certificate.'};(HERE/(prefix+'.json')).write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
