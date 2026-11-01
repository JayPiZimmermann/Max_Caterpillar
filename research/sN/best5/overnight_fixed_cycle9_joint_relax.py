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
    bools=0;debug=[]
    for ci,cell in enumerate(cells.values()):
        act=cell['active'];tops=sorted(cell['tops']);q=len(tops)==2;normal=[Q(i==tops[0])-Q(i==tops[1])for i in range(N)]if q else None;base=[Q(i==tops[-1])-Q(i==reference)for i in range(N)];g=[[dot([act[j][i]for j in range(m)],W[k])for i in range(N)]for k in range(K)];rgrad=[dot([act[j][i]for j in range(m)],R)for i in range(N)];feature_rays=sorted({tuple(sum(row[i]for i in S)for row in act)for S in cell['sets']});feature_rays=[v for v in feature_rays if any(v)];phases=[[z3.Bool(f'c{ci}_u{k}_{name}')for name in(('fp','fn','tp','tn')if q else('fp','fn'))]for k in range(K)];groups={(ids,(1,)+tail):z3.Bool(f'c{ci}_group_'+ '_'.join(map(str,ids))+'_'+ '_'.join(map(str,(1,)+tail)))for size in range(2,K+1)for ids in combinations(range(K),size)if len({signs[k]for k in ids})==2 for tail in product((1,-1),repeat=size-1)};bools+=sum(map(len,phases))+len(groups);debug.append((act,groups))
        for k in range(K):
            options=phases[k]+[v for(ids,eps),v in groups.items()if k in ids];solver.add(z3.PbEq([(b,1)for b in options],1));fp,fn=phases[k][:2];solver.add(z3.Implies(fp,z3.And([dot(v,W[k])>=0 for v in feature_rays])));solver.add(z3.Implies(fn,z3.And([dot(v,W[k])<=0 for v in feature_rays])))
            if q:
                tp,tn=phases[k][2:];pivot=next(i for i,x in enumerate(normal)if x);lam=g[k][pivot];parallel=z3.And([g[k][i]==rat(normal[i])*lam for i in range(1,N)]);solver.add(z3.Implies(tp,z3.And(parallel,lam>=0)));solver.add(z3.Implies(tn,z3.And(parallel,lam<=0)))
        for(ids,eps),b in groups.items():solver.add(z3.Implies(b,z3.And([z3.Sum([signs[k]*e*g[k][i]for k,e in zip(ids,eps)])==0 for i in range(1,N)])))
        if q:
            pivot=next(i for i,x in enumerate(normal)if x);solver.add(z3.Sum([signs[k]*(z3.If(phases[k][2],g[k][pivot],0)-z3.If(phases[k][3],g[k][pivot],0))for k in range(K)])==1)
        for i in range(1,N):
            terms=[rgrad[i]]+[z3.If(phases[k][0],signs[k]*g[k][i],0)for k in range(K)]+([z3.If(phases[k][3],signs[k]*g[k][i],0)for k in range(K)]if q else[])+[z3.If(b,rat(Q(1,2))*z3.Sum([signs[k]*g[k][i]for k in ids]),0)for(ids,eps),b in groups.items()];solver.add(z3.Sum(terms)==rat(base[i]))
    smt=HERE/f'overnight_fixed_cycle9_joint_relax_o{orientation}_{mode}.smt2';smt.write_text(solver.to_smt2());print('ENCODED',mode,'cells',len(cells),'real_variables',(K+1)*m,'booleans',bools,'assertions',len(solver.assertions()),'seconds',time.monotonic()-start,flush=True);res=solver.check();report={'status':str(res),'mode':mode,'orientation_index':orientation,'comparison_edges':edges,'z3_version':z3.get_version_string(),'cells':len(cells),'real_variables':(K+1)*m,'boolean_variables':bools,'assertions':len(solver.assertions()),'seconds':time.monotonic()-start,'budget_seconds':budget,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest(),'scope':'Constructive four-free-term core using five C5 comparison functions and the linear form x2−x0; physical first layer has four coordinate-anchor rows. Unbounded real coefficients; arbitrary target-wall groups; arbitrary signed-group linear relaxation. Collinearity/common orientation are omitted and independently diagnosed. No lower carrier bridge is claimed. Only independently globally checked SAT networks are constructions.'}
    if res==z3.sat:
        model=solver.model()
        def value(x):v=model.eval(x,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
        wc=[[value(x)for x in row]for row in W];rc=[value(x)for x in R];head=rc[:5]+[1-rc[5],-1+rc[5],rc[5],-rc[5]];physical_core=[row[:5]+[-row[5],row[5],row[5],-row[5]]for row in wc];nn={'N':N,'first_layer':net['first_layer'],'second_layer':[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,row))for row in physical_core],'output':['1','-1']+list(map(str,signs))};outpath=HERE/f'overnight_fixed_cycle9_joint_relax_o{orientation}_{mode}_network.json';outpath.write_text(json.dumps(nn,sort_keys=True,indent=2)+'\n');bad=[]
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
    report['statistics']=str(solver.statistics());(HERE/f'overnight_fixed_cycle9_joint_relax_o{orientation}_{mode}.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='statistics'},sort_keys=True),flush=True)
if __name__=='__main__':main()
