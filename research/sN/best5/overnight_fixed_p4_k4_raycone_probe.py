"""Exact arrangement-ray cone strengthening for the known sampled K4 case."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,math,time
import numpy as np
from scipy.optimize import linprog
import overnight_root9_equations as E
from overnight_fixed_k2_certify import certified_feasible
import exact_lp


def ray_kernel(rows,d):
    if d==1:return(1,)
    M=[list(map(Q,r))for r in rows];rank=0;piv=[]
    for col in range(d):
        i=next((i for i in range(rank,len(M))if M[i][col]),None)
        if i is None:continue
        M[rank],M[i]=M[i],M[rank];v=M[rank][col];M[rank]=[x/v for x in M[rank]]
        for i in range(len(M)):
            if i==rank:continue
            v=M[i][col];M[i]=[x-v*y for x,y in zip(M[i],M[rank])]
        piv.append(col);rank+=1
    if rank!=d-1:return None
    free=next(i for i in range(d)if i not in piv);out=[Q(i==free)for i in range(d)]
    for i,col in enumerate(piv):out[col]=-M[i][free]
    den=math.lcm(*(v.denominator for v in out));out=[int(v*den)for v in out];g=math.gcd(*out)
    if next(v for v in out if v)<0:g=-g
    return tuple(v//g for v in out)


def main():
    started=time.monotonic();E.initialize();zs=(23655,30836,31220,32316);ds=(1,-1,1,1);blocks=[];data=[]
    for z in zs:
        forms=E.arithmetic.flat(z)[0];d=len(E.arithmetic.BASES[z]);assert len(E.arithmetic.rref(forms))==d
        rays=sorted({v for rows in combinations(forms,d-1)if(v:=ray_kernel(rows,d))is not None});absolute=[[abs(sum(a*b for a,b in zip(f,r)))for f in forms]for r in rays];blocks.append((rays,absolute));data.append({'flat':z,'dimension':d,'forms':len(forms),'rays':rays})
    eq,forms,_=E.case_data(zs,ds);offset=[0]
    for z in zs:offset.append(offset[-1]+len(E.arithmetic.flat(z)[0]))
    rows=[];rhs=[]
    for i in range(49):
        e,b=eq(i);rows.append([sum(e.get(offset[k]+j,Q(0))*v for j,v in enumerate(ray))for k,(rays,absolute)in enumerate(blocks)for ray in absolute]);rhs.append(b)
    n=len(rows[0]);EE=[(['e',i],[-b]+r)for i,(r,b)in enumerate(zip(rows,rhs))];II=[(['y',i],[Q(0)]+[Q(i==j)for j in range(n)])for i in range(n)];feasible,proof=certified_feasible(EE,II,n);report={'status':'RAYCONE_RELAXATION_SURVIVOR'if feasible else'EXACT_RAYCONE_EXCLUSION','flats':zs,'signs':ds,'ray_variables':n,'blocks':data}
    if not feasible:
        eqw={i:Q(c)for(typ,i),c in proof if typ=='e'};combo=[sum(c*rows[i][j]for i,c in eqw.items())for j in range(n)];b=sum(c*rhs[i]for i,c in eqw.items());assert b>0 and all(v<=0 for v in combo);report['equation_template']=[[i,str(c/b)]for i,c in sorted(eqw.items())]
    else:
        r=linprog(np.zeros(n),A_eq=np.array(rows,float),b_eq=np.array(rhs,float),bounds=(0,None),method='highs');assert r.success;supp=[j for j,v in enumerate(r.x)if v>1e-9];sol=exact_lp.solve_eq([[-b]+[row[j]for j in supp]for row,b in zip(rows,rhs)],len(supp));assert sol is not None and all(v>=0 for v in sol);assert all(sum(v*row[j]for j,v in zip(supp,sol))==b for row,b in zip(rows,rhs));report['exact_ray_weights']=[[j,str(v)]for j,v in zip(supp,sol)if v]
    report.update(seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='blocks'},sort_keys=True,indent=2))
if __name__=='__main__':main()
