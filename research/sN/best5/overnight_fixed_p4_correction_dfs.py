"""Exact cell-based two-ReLU completion of three fixed positive carriers.

On each full first-layer cell, the correction is convex with0,1,or2
hyperplanes. Two positive ReLUs can only have those hyperplanes or fixed
sign. Every such assignment gives closed real linear constraints. No
coefficient box or input sample occurs. A successful network is globally
checked independently before being reported.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,product
import sys,json,time,signal,hashlib
import numpy as np
from scipy.optimize import linprog
import exact_lp
from overnight_fixed_k2_certify import certified_feasible
from overnight_fixed_cross_verify import check as globalcheck
HERE=Path(__file__).resolve().parent


def main():
    config=int(sys.argv[1]);budget=int(sys.argv[2])if len(sys.argv)>2 else 60;start=time.monotonic();net=json.loads((HERE/'overnight_fixed_cross_net9_14_simple.json').read_text());A=[[Q(x)for x in r]for r in net['first_layer'][:7]];W=[[Q(x)for x in r[:7]]for r in net['second_layer'][2:]];D=list(map(Q,net['output'][2:]));R0=list(map(Q,net['second_layer'][0][:7]));choices=list(product((0,1),(0,1),(0,-1),(0,-1),(0,1)));p13,p14,q14,r14,last=choices[config];plus=[[Q(x)for x in r]for r in [[1,0,p13,-1,0,0,0],[1,0,p14,0,-1,q14,r14],([0,0,0,0,0,1,-1]if last==0 else[0,1,0,-1,0,0,0])]];cells={}
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};act=[row if rank[next(i for i,x in enumerate(row)if x>0)]<rank[next(i for i,x in enumerate(row)if x<0)]else[Q(0)]*5 for row in A];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'key':key,'active':act,'sets':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,5))
    for cell in cells.values():
        act=cell['active'];linear=[-sum(w*row[i]for w,row in zip(R0,act))for i in range(5)];curv={}
        for w,d in zip(W+plus,[-d for d in D]+[Q(1)]*3):
            g=tuple(sum(w[j]*act[j][i]for j in range(7))for i in range(5));vs=[sum(g[j]for j in S)for S in cell['sets']]
            if min(vs)>=0:linear=[x+d*y for x,y in zip(linear,g)]
            elif max(vs)<=0:pass
            else:
                sc=next(x for x in g if x);normal=tuple(x/sc for x in g);curv[normal]=curv.get(normal,Q(0))+d*abs(sc)
                if sc<0:linear=[x+d*y for x,y in zip(linear,g)]
        cell['linear']=linear;cell['curvature']=[(g,c)for g,c in sorted(curv.items())if c];assert len(cell['curvature'])<=2 and all(c>0 for g,c in cell['curvature'])
    # High-rank cells with nonzero target curvature impose the sharpest equalities.
    ordered=sorted(cells.values(),key=lambda c:(len(c['curvature']),sum(c['key']),len(c['sets'])),reverse=True);systems=[]
    for ci,cell in enumerate(ordered):
        act=cell['active'];curv=cell['curvature'];cats=[('p',0),('n',0)]+[(j,s)for j in range(len(curv))for s in(1,-1)];opts=[]
        hg=[[[Q(0)]*(7*k)+[act[j][i]for j in range(7)]+[Q(0)]*(14-7*k)for i in range(5)]for k in range(2)];rg=[[Q(0)]*14+[act[j][i]for j in range(7)]for i in range(5)]
        for catpair in product(cats,repeat=2):
            if any(not any(cat[0]==j for cat in catpair)for j in range(len(curv))):continue
            EE=[];II=[];lin=[row[:]for row in rg];amplitudes=[[Q(0)]*21 for _ in curv]
            for k,(kind,s)in enumerate(catpair):
                if kind in('p','n'):
                    sign=1 if kind=='p'else-1
                    for S in sorted(cell['sets']):II.append([Q(0)]+[sign*sum(hg[k][i][j]for i in S)for j in range(21)])
                    if kind=='p':lin=[[x+y for x,y in zip(row,g)]for row,g in zip(lin,hg[k])]
                else:
                    normal,c=curv[kind];pivot=next(i for i,v in enumerate(normal)if v);amp=hg[k][pivot]
                    for i in range(5):EE.append([Q(0)]+[x-normal[i]*y for x,y in zip(hg[k][i],amp)])
                    II.append([Q(0)]+[s*x for x in amp]);amplitudes[kind]=[x+s*y for x,y in zip(amplitudes[kind],amp)]
                    if s<0:lin=[[x+y for x,y in zip(row,g)]for row,g in zip(lin,hg[k])]
            EE +=[[-c]+row for row,(g,c)in zip(amplitudes,curv)];EE +=[[-b]+row for row,b in zip(lin,cell['linear'])]
            if any(row[0]and not any(row[1:])for row in EE):continue
            EE=[row for row in EE if any(row)];II=[row for row in II if any(row)];opts.append((catpair,EE,II))
        systems.append(opts)
    counts={'nodes':0,'leaves':0,'splits':0};solution=None;signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('declared budget')));signal.alarm(budget)
    def dfs(depth,EE,II):
        nonlocal solution
        counts['nodes']+=1
        if counts['nodes']>5000:raise TimeoutError('node budget')
        feasible,proof=certified_feasible(EE,II,21)
        if not feasible:counts['leaves']+=1;return['cone',proof]
        if depth==len(systems):
            er=[r for _,r in EE];ir=[r for _,r in II];res=linprog(np.zeros(21),A_eq=np.array([r[1:]for r in er],float),b_eq=np.array([-r[0]for r in er],float),A_ub=-np.array([r[1:]for r in ir],float),b_ub=np.array([r[0]for r in ir],float),bounds=(None,None),method='highs');assert res.success;active=[r for r in ir if abs(float(r[0])+sum(float(c)*v for c,v in zip(r[1:],res.x)))<1e-8];sol=exact_lp.solve_eq(er+active,21);assert sol is not None and all(r[0]+sum(c*v for c,v in zip(r[1:],sol))==0 for r in er)and all(r[0]+sum(c*v for c,v in zip(r[1:],sol))>=0 for r in ir);solution=sol;return['solution',list(map(str,sol))]
        counts['splits']+=1;node=['cell',depth]
        for oi,(cats,eq,ineq)in enumerate(systems[depth]):
            ee=EE+[(['e',depth,oi,j],r)for j,r in enumerate(eq)];ii=II+[(['i',depth,oi,j],r)for j,r in enumerate(ineq)];node.append(dfs(depth+1,ee,ii))
            if solution is not None:break
        return node
    try:proof=dfs(0,[],[]);status='EXACT_COMPLETION_CANDIDATE'if solution is not None else'EXACT_THREE_CARRIER_COMPLETION_EXCLUDED'
    except TimeoutError as exc:proof=None;status=str(exc)
    finally:signal.alarm(0)
    out={'config':config,'parameters':choices[config],'status':status,'counts':counts,'proof':proof,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if solution is not None:
        h1,h2=solution[:7],solution[7:14];R=[-x for x in solution[14:]];head=R+[Q(1),Q(-1)];nn=json.loads(json.dumps(net));nn['second_layer']=[list(map(str,head)),list(map(str,[-x for x in head]))]+[list(map(str,row+[Q(0)]*2))for row in plus+[h1,h2]];nn['output']=['1','-1','1','1','1','-1','-1'];path=HERE/f'overnight_fixed_p4_correction_net_{config}.json';path.write_text(json.dumps(nn,sort_keys=True,indent=2)+'\n');out['global_check']=globalcheck(path)
    (HERE/f'overnight_fixed_p4_correction_dfs_{config}.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='proof'},sort_keys=True),flush=True)
if __name__=='__main__':main()
