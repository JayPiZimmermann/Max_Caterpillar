"""Exact smallest gate retaining the next symmetric pair-infinity coefficient.

omega=(z-S/2,-z-S/2,xi), S=sum(xi); full orbit sums are even in z.
The leading projection was exactly refuted on two stars. This controlled gate
retains z^-4 as well as z^-2, checking z^-3 vanishes and the old leading result.
No arity extrapolation. Domain all10 canonical5-label star orbit columns.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time
import sympy as S
from dfs_review_fourier import family
from overnight_uniform_pruning_infinity import normal_factors
from overnight_uniform_pruning_gate import evaluate

HERE=Path(__file__).parent

def direct_coefficients(unit,xi):
    n=len(xi)+2;fac=normal_factors(unit,n);base=[-Q(sum(xi),2)]*2+list(map(Q,xi));slope=[1,-1]+[0]*len(xi);sums=[Q(0)]*3
    for p in itertools.permutations(range(n)):
        b=[base[i] for i in p];d=[slope[i] for i in p];numdegree=n-4 if d[0] else 0;den=Q(1);dd=0;ratios=[]
        for C,h in fac:
            q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
            for k in [h,h+1]:
                c=q0+k*b[0];t=q1+k*d[0]
                if t:dd+=1;den*=t;ratios.append(c/t)
                else:assert c;den*=c
        gap=dd-numdegree;assert gap>=2
        if gap>4:continue
        total=sum(ratios);inverse=[Q(1),-total,(total*total+sum(r*r for r in ratios))/2]
        if d[0]:
            numerator=[Q((-d[0])**(n-4)*math.comb(n-4,j))*(b[0]/d[0])**j if j<=n-4 else Q(0) for j in range(3)]
        else:numerator=[(-b[0])**(n-4),Q(0),Q(0)]
        for h in [2,3,4]:
            j=h-gap
            if j>=0:sums[h-2]+=sum(numerator[k]*inverse[j-k] for k in range(j+1))/den
    assert sums[1]==0
    assert sums[0]==evaluate(unit,xi)
    return sums[0],sums[2]

def main():
    start=time.monotonic();units=[{'root':u['root'],'edges':u['edges']} for u in family(5,'nopath')];points=[];rows=[]
    for r,s in [(2,11),(3,13),(4,17),(5,19),(6,23),(7,29),(8,31),(9,37),(10,41),(11,43)]:
        xi=[1,r,s];data=[direct_coefficients(u,xi) for u in units];J=Q(-1,math.prod(xi));targets=[J,Q(sum(xi)**2,4)*J]
        for k in range(2):rows.append([v[k] for v in data]+[targets[k]]);points.append({'xi':xi,'inverse_power':2+2*k})
    A=S.Matrix(rows);ranks=[A[:,:-1].rank(),A.rank()];result={'status':'EXACT_TWO_JET_STAR_GATE','arity':5,'ranks':ranks,'points':points,'rows':[[str(v) for v in r] for r in rows],'units':units,'controls':['odd inverse coefficient vanishes','leading coefficient agrees with independently derived contraction recursion']}
    if ranks[0]<ranks[1]:
        w=next(w for w in A[:,:-1].T.nullspace() if (w.T*A[:,-1])[0]);w/=(w.T*A[:,-1])[0]
        assert w.T*A[:,:-1]==S.zeros(1,len(units)) and(w.T*A[:,-1])[0]==1
        result['weights']=list(map(str,w));result['scope']='Exact finite separator retaining two jets at5 labels only; no uniform matching theorem.'
    else:
        c,pars=A[:,:-1].gauss_jordan_solve(A[:,-1]);c=c.subs({p:0 for p in pars});result['combination']=list(map(str,c));result['scope']='No gap on this exact finite grid; not an all-frequency identity.'
    result['seconds']=time.monotonic()-start
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],ranks,result['seconds'],flush=True)
if __name__=='__main__':main()
