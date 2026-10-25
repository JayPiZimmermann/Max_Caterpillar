"""Unbounded closed-sign test of the eight remaining regroup families."""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations
import json,time,signal,hashlib
import numpy as np
from scipy.optimize import linprog
import exact_lp
from overnight_fixed_k2_certify import certified_feasible
from overnight_fixed_cross_verify import check as globalcheck
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();net=json.loads((HERE/'overnight_fixed_cross_net9_14_simple.json').read_text());A=[[Q(x)for x in r]for r in net['first_layer'][:7]];W=[[Q(x)for x in r[:7]]for r in net['second_layer'][2:]];D=list(map(Q,net['output'][2:]));cells={}
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};act=[]
        for row in A:
            i=next(i for i,x in enumerate(row)if x>0);j=next(i for i,x in enumerate(row)if x<0);act.append(row if rank[i]<rank[j]else[Q(0)]*5)
        key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'sets':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,5))
    sets=sorted({S for cell in cells.values()for S in cell['sets']});Z=[[max(sum(row[i]for i in S),Q(0))for row in A]for S in sets];si={S:i for i,S in enumerate(sets)};results=[];nodes=0;signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('90 second budget')));signal.alarm(90)
    try:
      for candidate in json.loads((HERE/'overnight_fixed_p4_regroup_exact.json').read_text())['results']:
        inds=candidate['indices'];d=candidate['curvature_sign'];target=[sum(D[k]*max(sum(w*x for w,x in zip(W[k],z)),Q(0))for k in inds)for z in Z]
        for rawfam in candidate['families']:
          fam=[list(map(Q,row))for row in rawfam]
          if len(fam)==7:continue
          piv=[next(i for i,v in enumerate(row[:-1])if v)for row in fam];free=[i for i in range(7)if i not in piv];h0=[Q(0)]*7;H=[[Q(i==j)for i in range(7)]for j in free]
          for p,row in zip(piv,fam):
            h0[p]=row[-1]
            for k,j in enumerate(free):H[k][p]=-row[j]
          hv=[[sum(c*x for c,x in zip(h0,z))]+[sum(c*x for c,x in zip(h,z))for h in H]for z in Z];dim=len(free);n=7+dim;linear_cells=[]
          for key,cell in cells.items():
            curv={};act=cell['active']
            for k in inds:
                g=tuple(sum(W[k][j]*act[j][i]for j in range(7))for i in range(5));v=[sum(g[j]for j in S)for S in cell['sets']]
                if min(v)<0<max(v):
                    sc=next(x for x in g if x);normal=tuple(x/sc for x in g);curv[normal]=curv.get(normal,Q(0))+D[k]*abs(sc)
            if not any(curv.values()):linear_cells.append(tuple(si[S]for S in sorted(cell['sets'])))
          initial={j:(1 if row[0]>=0 else-1)for j,row in enumerate(hv)if not any(row[1:])};lc={'nodes':0,'leaves':0,'splits':0};solution=None
          def dfs(signs,pending,I):
            nonlocal nodes,solution
            lc['nodes']+=1;nodes+=1;EE=[]
            for j,s in sorted(signs.items()):
                row=[-target[j]]+Z[j]+[Q(0)]*dim
                if s==1:row[0]+=d*hv[j][0];row[8:]=[d*v for v in hv[j][1:]]
                EE.append((['e',j],row))
            feasible,proof=certified_feasible(EE,I,n)
            if not feasible:lc['leaves']+=1;return['cone',proof]
            pending=[cs for cs in pending if not(all(j in signs for j in cs)and len({signs[j]for j in cs})==1)]
            if not pending:
                assert len(signs)==len(sets);er=[row for _,row in EE];ir=[row for _,row in I];res=linprog(np.zeros(n),A_eq=np.array([row[1:]for row in er],float),b_eq=np.array([-row[0]for row in er],float),A_ub=-np.array([row[1:]for row in ir],float)if ir else None,b_ub=np.array([row[0]for row in ir],float)if ir else None,bounds=(None,None),method='highs');assert res.success;active=[row for row in ir if abs(float(row[0])+sum(float(c)*v for c,v in zip(row[1:],res.x)))<1e-8];sol=exact_lp.solve_eq(er+active,n);assert sol is not None and all(row[0]+sum(c*v for c,v in zip(row[1:],sol))==0 for row in er)and all(row[0]+sum(c*v for c,v in zip(row[1:],sol))>=0 for row in ir);solution=sol;return['feasible',[str(v)for v in sol]]
            cs=max(pending,key=lambda cs:sum(j not in signs for j in cs));rest=[c for c in pending if c!=cs];tree=['cell',list(cs)];lc['splits']+=1
            for s in(1,-1):
                ss=dict(signs);II=list(I)
                for j in cs:
                    ss.setdefault(j,s);II.append((['s',j,s],[s*hv[j][0]]+[Q(0)]*7+[s*v for v in hv[j][1:]]))
                tree.append(dfs(ss,rest,II))
                if solution is not None:break
            return tree
          tree=dfs(initial,linear_cells,[]);out={'indices':inds,'sign':d,'family':rawfam,'counts':lc,'tree':tree,'status':'EXACT_SIGN_EXCLUDED'if solution is None else'EXACT_IDENTITY_CANDIDATE'}
          if solution is not None:
            h=[h0[i]+sum(solution[7+k]*H[k][i]for k in range(dim))for i in range(7)];rem=solution[:7];head=list(map(Q,net['second_layer'][0]));head[:7]=[x+y for x,y in zip(head[:7],rem)];nn=json.loads(json.dumps(net));nn['second_layer']=[list(map(str,head)),list(map(str,[-v for v in head]))]+[list(map(str,W[k]+[Q(0)]*2))for k in range(12)if k not in inds]+[list(map(str,h+[Q(0)]*2))];nn['output']=['1','-1']+[str(D[k])for k in range(12)if k not in inds]+[str(d)];path=HERE/f'overnight_fixed_p4_regroup_new_{len(results)}.json';path.write_text(json.dumps(nn,sort_keys=True,indent=2)+'\n');out['global_check']=globalcheck(path)
          results.append(out);print('FAMILY',inds,dim,lc,out['status'],'seconds',time.monotonic()-start,flush=True)
    except TimeoutError:print('BUDGET_STOP',flush=True)
    finally:signal.alarm(0)
    out={'status':'BOUNDED_REMAINING_REGROUP_FAMILIES','results':results,'nodes':nodes,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_p4_regroup_remaining.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print('DONE',len(results),nodes,time.monotonic()-start,flush=True)
if __name__=='__main__':main()
