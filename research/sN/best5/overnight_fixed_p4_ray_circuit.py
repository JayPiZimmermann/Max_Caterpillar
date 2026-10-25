"""Closed three-way triangle-facet proof for one exact ray-cone survivor.

A circuit f0+f1=f2 forces one weighted absolute value to be the sum
of the other two. Each branch is a face of the absolute ray cone, so
only generators on that face remain. No numerical infeasibility is trusted.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import combinations
import json,time,signal,math,hashlib
import numpy as np
from scipy.optimize import linprog
import exact_lp
import overnight_root9_equations as E
from overnight_fixed_k2_certify import certified_feasible
HERE=Path(__file__).resolve().parent


def circuits(forms):
    result=[]
    for inds in combinations(range(len(forms)),3):
        rows=[forms[j]for j in inds]
        if len(E.arithmetic.rref(rows))!=2 or any(len(E.arithmetic.rref([rows[i],rows[j]]))<2 for i,j in combinations(range(3),2)):continue
        p,q=next((p,q)for p,q in combinations(range(len(rows[0])),2)if rows[0][p]*rows[1][q]-rows[0][q]*rows[1][p]);c=[rows[1][p]*rows[2][q]-rows[1][q]*rows[2][p],rows[2][p]*rows[0][q]-rows[2][q]*rows[0][p],rows[0][p]*rows[1][q]-rows[0][q]*rows[1][p]];assert all(sum(c[j]*rows[j][t]for j in range(3))==0 for t in range(len(rows[0])));result.append((inds,tuple(abs(x)for x in c)))
    return result


def main():
    start=time.monotonic();E.initialize();w=json.loads((HERE/'overnight_fixed_p4_k4_raylearn_survivor.json').read_text());zs=w['flats'];ds=w['signs'];fans={r['flat']:r['rays']for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};absolute=[];blocks=[];allcircuits=[];eq=E.case_data(zs,ds)[0];rhs=[eq(i)[1]for i in range(49)]
    for z in zs:
        forms=E.arithmetic.flat(z)[0];vals=[[abs(sum(a*b for a,b in zip(f,r)))for f in forms]for r in fans[z]];absolute.append(vals);local=E.case_data((z,),(1,))[0];blocks.append([[sum(c*ray[j]for j,c in local(i)[0].items())for ray in vals]for i in range(49)]);cs=[]
        for inds,c in circuits(forms):
            slacks=[[sum(c[t]*v[inds[t]]for t in range(3))-2*c[j]*v[inds[j]]for j in range(3)]for v in vals];assert all(x>=0 for row in slacks for x in row);cs.append((inds,c,slacks))
        allcircuits.append(cs)
    counts={'nodes':0,'leaves':0,'branches':0};openw=None
    def dfs(allowed,depth=0):
        nonlocal openw
        counts['nodes']+=1;assert counts['nodes']<=1000,'node budget';cols=[(k,j)for k,js in enumerate(allowed)for j in js];rows=[[ds[k]*blocks[k][i][j]for k,j in cols]for i in range(49)];n=len(cols)
        EE=[(['e',i],[-rhs[i]]+rows[i])for i in range(49)];II=[(['y',j],[Q(0)]+[Q(j==k)for k in range(n)])for j in range(n)];feasible,proof=certified_feasible(EE,II,n)
        if not feasible:
            eqw={i:Q(c)for(typ,i),c in proof if typ=='e'};b=sum(c*rhs[i]for i,c in eqw.items());assert b>0;t=[(i,c/b)for i,c in sorted(eqw.items())if c];assert all(sum(c*rows[i][j]for i,c in t)<=0 for j in range(n));counts['leaves']+=1;return ['cone',[[i,str(c)]for i,c in t]]
        r=linprog(np.zeros(n),A_eq=np.array(rows,float),b_eq=np.array(rhs,float),bounds=(0,None),method='highs');assert r.success;supp=[j for j,v in enumerate(r.x)if v>1e-9];sol=exact_lp.solve_eq([[-rhs[i]]+[rows[i][j]for j in supp]for i in range(49)],len(supp));assert sol is not None and all(v>=0 for v in sol);assert all(sum(v*rows[i][j]for j,v in zip(supp,sol))==rhs[i]for i in range(49));weights={cols[j]:v for j,v in zip(supp,sol)if v};choices=[]
        for k,cs in enumerate(allcircuits):
            for ci,(inds,c,slacks)in enumerate(cs):
                deficits=[sum(weights.get((k,j),Q(0))*slacks[j][t]for j in allowed[k])for t in range(3)]
                if min(deficits)>0:
                    children=[tuple(j for j in allowed[k]if slacks[j][t]==0)for t in range(3)];choices.append((max(map(len,children)),sum(map(len,children)),k,ci,children))
        if not choices:
            openw={'allowed':allowed,'weights':[[k,j,str(v)]for(k,j),v in weights.items()],'depth':depth};return ['open']
        _,_,k,ci,children=min(choices);inds,c,_=allcircuits[k][ci];counts['branches']+=1;tree=['triangle',k,list(inds),[str(v)for v in c]]
        for child in children:
            aa=list(allowed);aa[k]=child;tree.append(dfs(tuple(aa),depth+1))
            if openw:break
        return tree
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('120 second budget')));signal.alarm(120)
    try:tree=dfs(tuple(tuple(range(len(fans[z])))for z in zs));status='EXACT_CLOSED_TRIANGLE_PROOF'if openw is None else'EXACT_TRIANGLE_RELAXATION_SURVIVOR'
    except(TimeoutError,AssertionError)as exc:print('STOP',repr(exc),flush=True);tree=None;status='INCOMPLETE'
    finally:signal.alarm(0)
    out={'status':status,'flats':zs,'signs':ds,'counts':counts,'tree':tree,'open_witness':openw,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_p4_ray_circuit.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('tree','open_witness')},sort_keys=True),flush=True)
if __name__=='__main__':main()
