"""Joint four-core proposal on C5 with arbitrary signed-group cancellation.

A linear-real necessary relaxation: each spurious group has zero signed
sum of oriented gradients. Common orientation and collinearity are not
assumed by the solver; every SAT model is globally checked, and failures
record the exact missing quadratic constraints. No coefficient bounds.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,combinations,product
import json,sys,time,hashlib,resource
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_anchor_verify import check as globalcheck
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
    smt=HERE/f'overnight_fixed_cycle9_local_proposal_o{orientation}_{mode}.smt2';smt.write_text(solver.to_smt2());print('ENCODED',mode,'cells',len(cells),'real_variables',(K+1)*m,'booleans',bools,'assertions',len(solver.assertions()),'seconds',time.monotonic()-start,flush=True);res=solver.check();report={'status':str(res),'mode':mode,'orientation_index':orientation,'comparison_edges':edges,'z3_version':z3.get_version_string(),'cells':len(cells),'real_variables':(K+1)*m,'boolean_variables':bools,'assertions':len(solver.assertions()),'seconds':time.monotonic()-start,'budget_seconds':budget,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest(),'scope':'Constructive four-free-term core using five C5 comparison functions and the linear form x2−x0; physical first layer has four coordinate-anchor rows. Unbounded real coefficients; 31 exact Boolean-value and26 generic-tie necessary equations only. No global sufficiency is claimed. No lower carrier bridge is claimed. Only independently globally checked SAT networks are constructions.'}
    if res==z3.sat:
        model=solver.model()
        def value(x):v=model.eval(x,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
        wc=[[value(x)for x in row]for row in W];rc=[value(x)for x in R];head=rc[:5]+[1-rc[5],-1+rc[5],rc[5],-rc[5]];physical_core=[row[:5]+[-row[5],row[5],row[5],-row[5]]for row in wc];nn={'N':N,'first_layer':net['first_layer'],'second_layer':[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,row))for row in physical_core],'output':['1','-1']+list(map(str,signs))};outpath=HERE/f'overnight_fixed_cycle9_local_proposal_o{orientation}_{mode}_network.json';outpath.write_text(json.dumps(nn,sort_keys=True,indent=2)+'\n');bad=[]
        for ci,(act,groups)in enumerate(debug):
            for(ids,eps),b in groups.items():
                if not z3.is_true(model.eval(b,model_completion=True)):continue
                oriented=[[e*sum(wc[k][j]*act[j][i]for j in range(m))for i in range(N)]for k,e in zip(ids,eps)];issues=[]
                for u,v in combinations(range(len(ids)),2):
                    dotvalue=sum(x*y for x,y in zip(oriented[u],oriented[v]));minors=[(i,j,oriented[u][i]*oriented[v][j]-oriented[u][j]*oriented[v][i])for i,j in combinations(range(N),2)];minors=[(i,j,str(v))for i,j,v in minors if v]
                    if dotvalue<0 or minors:issues.append({'units':[ids[u],ids[v]],'dot':str(dotvalue),'nonzero_minors':minors})
                if issues:bad.append({'cell':ci,'units':ids,'orientations':eps,'gradients':[list(map(str,g))for g in oriented],'issues':issues})
        report['bad_groups']=bad
        try:report['global_check']=globalcheck(outpath)
        except AssertionError as exc:report['status']='SAT_RELAXATION_COUNTERMODEL';report['global_failure']=str(exc)
    elif res==z3.unknown:report['reason_unknown']=solver.reason_unknown()
    report['statistics']=str(solver.statistics());(HERE/f'overnight_fixed_cycle9_local_proposal_o{orientation}_{mode}.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='statistics'},sort_keys=True),flush=True)
if __name__=='__main__':main()
