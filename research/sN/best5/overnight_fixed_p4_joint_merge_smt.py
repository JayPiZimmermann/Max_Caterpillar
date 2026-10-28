"""Joint continuous five-core proposal via finite cell incidences.

All preactivations and the W7 remainder vary over unbounded real space.
Target-wall groups may have any size. Spurious walls are restricted to
pairwise positive/negative cancellation and2:1 three-unit merges. This is a constructive submodel,
not a complete five-unit lower-bound test. Any SAT network is subjected
to the independent global checker before being accepted.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,combinations
import json,sys,time,hashlib,resource
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_cross_verify import check as globalcheck
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();mode=sys.argv[1]if len(sys.argv)>1 else'p3';budget=int(sys.argv[2])if len(sys.argv)>2 else 120;resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));z3.set_param('parallel.enable',False);path=HERE/('netB_10_6.json'if mode=='control'else'overnight_fixed_cross_net9_14_simple.json');net=json.loads(path.read_text());N=5;A=[list(map(Q,row))for row in net['first_layer'][:-2]];m=len(A);reference=next(i for i,v in enumerate(net['first_layer'][-2])if Q(v));cells={}
    for p in permutations(range(N)):
        rank={v:i for i,v in enumerate(p)};act=[row if rank[next(i for i,x in enumerate(row)if x>0)]<rank[next(i for i,x in enumerate(row)if x<0)]else[Q(0)]*N for row in A];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'sets':set(),'tops':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,N));cell['tops'].add(p[0])
    for cell in cells.values():assert len(cell['tops'])<=2
    signs=([1,1,1,-1,-1]if mode=='control'else[1]*int(mode[1:])+[-1]*(5-int(mode[1:])));constants=None
    if mode=='control':
        constants=[];Rconst=list(map(Q,net['second_layer'][0][:-2]))
        for row,raw in zip(net['second_layer'][2:],net['output'][2:]):
            d=Q(raw);w=[abs(d)*Q(v)for v in row[:-2]];s=1 if d>0 else-1
            if w[0]<0:Rconst=[r+s*v for r,v in zip(Rconst,w)];w=[-v for v in w]
            constants.append((s,w))
        constants.sort(key=lambda sw:(-sw[0],sum((2**j)*v for j,v in enumerate(sw[1]))));signs=[s for s,w in constants]
    K=len(signs);positive=[k for k,d in enumerate(signs)if d>0];negative=[k for k,d in enumerate(signs)if d<0];W=[[z3.Real(f'w_{k}_{j}')for j in range(m)]for k in range(K)];R=[z3.Real(f'r_{j}')for j in range(m)];solver=z3.SolverFor('QF_LRA');solver.set(timeout=budget*1000);solver.set(max_memory=2500)
    def rat(v):v=Q(v);return z3.RealVal(f'{v.numerator}/{v.denominator}')
    def dot(a,b):return z3.Sum([rat(x)*y for x,y in zip(a,b)if x])
    if constants is not None:
        for k,(d,w)in enumerate(constants):solver.add(*[W[k][j]==rat(w[j])for j in range(m)])
        solver.add(*[R[j]==rat(Rconst[j])for j in range(m)])
    for row in W:solver.add(row[0]>=0)
    for group in(positive,negative):
        for k,l in zip(group,group[1:]):solver.add(z3.Sum([(2**j)*W[k][j]for j in range(m)])<=z3.Sum([(2**j)*W[l][j]for j in range(m)]))
    bools=0
    for ci,cell in enumerate(cells.values()):
        act=cell['active'];tops=sorted(cell['tops']);q=len(tops)==2;normal=[Q(i==tops[0])-Q(i==tops[1])for i in range(N)]if q else None;base=[Q(i==tops[-1])-Q(i==reference)for i in range(N)];g=[[dot([act[j][i]for j in range(m)],W[k])for i in range(N)]for k in range(K)];rgrad=[dot([act[j][i]for j in range(m)],R)for i in range(N)];feature_rays=sorted({tuple(sum(row[i]for i in S)for row in act)for S in cell['sets']});feature_rays=[v for v in feature_rays if any(v)];phases=[[z3.Bool(f'c{ci}_u{k}_{name}')for name in(('fp','fn','tp','tn')if q else('fp','fn'))]for k in range(K)];pairs={(p,n,o):z3.Bool(f'c{ci}_pair{p}_{n}_{o}')for p in positive for n in negative for o in(1,-1)};merges={(i,j,k,ej,ek):z3.Bool(f'c{ci}_merge{i}_{j}_{k}_{ej}_{ek}')for side,other in((positive,negative),(negative,positive))for i,j in combinations(side,2)for k in other for ej in(1,-1)for ek in(1,-1)};bools+=sum(map(len,phases))+len(pairs)+len(merges)
        for k in range(K):
            options=phases[k]+[v for(p,n,o),v in pairs.items()if k in(p,n)]+[v for(i,j,l,ej,ek),v in merges.items()if k in(i,j,l)];solver.add(z3.PbEq([(b,1)for b in options],1));fp,fn=phases[k][:2];solver.add(z3.Implies(fp,z3.And([dot(v,W[k])>=0 for v in feature_rays])));solver.add(z3.Implies(fn,z3.And([dot(v,W[k])<=0 for v in feature_rays])))
            if q:
                tp,tn=phases[k][2:];pivot=next(i for i,x in enumerate(normal)if x);lam=g[k][pivot];parallel=z3.And([g[k][i]==rat(normal[i])*lam for i in range(1,N)]);solver.add(z3.Implies(tp,z3.And(parallel,lam>=0)));solver.add(z3.Implies(tn,z3.And(parallel,lam<=0)))
        for(p,n,o),b in pairs.items():solver.add(z3.Implies(b,z3.And([g[p][i]==o*g[n][i]for i in range(1,N)])))
        for(i,j,k,ej,ek),b in merges.items():solver.add(z3.Implies(b,z3.And([g[j][t]==ej*g[i][t]for t in range(1,N)]+[g[k][t]==2*ek*g[i][t]for t in range(1,N)])))
        if q:
            pivot=next(i for i,x in enumerate(normal)if x);solver.add(z3.Sum([signs[k]*(z3.If(phases[k][2],g[k][pivot],0)-z3.If(phases[k][3],g[k][pivot],0))for k in range(K)])==1)
        for i in range(1,N):
            terms=[rgrad[i]]+[z3.If(phases[k][0],signs[k]*g[k][i],0)for k in range(K)]+([z3.If(phases[k][3],signs[k]*g[k][i],0)for k in range(K)]if q else[])+[z3.If(b,g[p][i],0)for(p,n,o),b in pairs.items()if o<0]+[z3.If(b,rat(Q(1,2))*(signs[j]*g[j][i]+signs[k]*g[k][i]+signs[l]*g[l][i]),0)for(j,k,l,ej,ek),b in merges.items()];solver.add(z3.Sum(terms)==rat(base[i]))
    smt=HERE/f'overnight_fixed_p4_joint_merge_smt_{mode}.smt2';smt.write_text(solver.to_smt2());print('ENCODED',mode,'cells',len(cells),'real_variables',(K+1)*m,'booleans',bools,'assertions',len(solver.assertions()),'seconds',time.monotonic()-start,flush=True);res=solver.check();report={'status':str(res),'mode':mode,'z3_version':z3.get_version_string(),'cells':len(cells),'real_variables':(K+1)*m,'boolean_variables':bools,'assertions':len(solver.assertions()),'seconds':time.monotonic()-start,'budget_seconds':budget,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'smt_sha256':hashlib.sha256(smt.read_bytes()).hexdigest(),'scope':'Unbounded real coefficients, arbitrary target-wall groups, pairwise and2:1 three-unit spurious cancellations only. UNSAT is not a general five-unit obstruction. Only independently globally checked SAT networks are constructions.'}
    if res==z3.sat:
        model=solver.model()
        def value(x):v=model.eval(x,model_completion=True);return Q(v.numerator_as_long(),v.denominator_as_long())
        wc=[[value(x)for x in row]for row in W];rc=[value(x)for x in R];head=rc+[Q(1),Q(-1)];nn={'N':N,'first_layer':net['first_layer'],'second_layer':[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,row+[Q(0)]*2))for row in wc],'output':['1','-1']+list(map(str,signs))};outpath=HERE/f'overnight_fixed_p4_joint_merge_smt_{mode}_network.json';outpath.write_text(json.dumps(nn,sort_keys=True,indent=2)+'\n');report['global_check']=globalcheck(outpath)
    elif res==z3.unknown:report['reason_unknown']=solver.reason_unknown()
    report['statistics']=str(solver.statistics());(HERE/f'overnight_fixed_p4_joint_merge_smt_{mode}.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='statistics'},sort_keys=True),flush=True)
if __name__=='__main__':main()
