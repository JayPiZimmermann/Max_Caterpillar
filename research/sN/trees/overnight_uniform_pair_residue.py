"""Exact five-label gate for all linear functionals of a paired-limit curve.

The old single evaluation of the t^-1 coefficient fails. This tests the entire
curve with base frequencies (0,1,-1,z,-z), slope (4,-1,-1,-1,-1), by exact rational
functions, to see whether secondary Laurent/contour functionals could separate.
All full canonical star roots/orientations are covered by the existing family
enumerator; arithmetic is symbolic over Q(z). Budget120seconds, one thread.
"""
from pathlib import Path
import itertools,json,math,time
import sympy as S
from dfs_review_fourier import family

def coefficient(unit,base,slope):
    a0,a1=base[0],slope[0];zeros=[];nonzero=[]
    for side,sign in unit['cuts']:
        q0=sum(base[i] for i in side);q1=sum(slope[i] for i in side)
        for c,d in [(q0,q1),(q0+sign*a0,q1+sign*a1)]:
            if c==0:assert d;zeros.append(d)
            else:nonzero.append((c,d))
    p=len(zeros)
    if not p:return S.Integer(0)
    series=[(-a0 if j==0 else -a1 if j==1 else S.Integer(0)) for j in range(p)]
    for c,d in nonzero:
        inv=[(-d)**j/c**(j+1) for j in range(p)]
        series=[sum(series[k]*inv[j-k] for k in range(j+1)) for j in range(p)]
    return series[p-1]/math.prod(zeros)

def main():
    start=time.monotonic();z=S.Symbol('z');base=[S.Integer(0),S.Integer(1),S.Integer(-1),z,-z];slope=[4,-1,-1,-1,-1]
    fam=family(5,'nopath');curves=[]
    for j,u in enumerate(fam):
        f=S.cancel(sum(coefficient(u,[base[i] for i in p],[slope[i] for i in p]) for p in itertools.permutations(range(5))))
        curves.append(f)
        print('column',j,'curve',S.factor(f),'seconds',time.monotonic()-start,flush=True)
    target=S.Rational(1,4)/z**2
    D=S.lcm([S.denom(f) for f in curves+[target]])
    polys=[S.Poly(S.cancel(D*f),z) for f in curves+[target]];degree=max(p.degree() for p in polys)
    A=S.Matrix([[p.nth(k) for p in polys[:-1]] for k in range(degree+1)]);b=S.Matrix([polys[-1].nth(k) for k in range(degree+1)])
    ranks=[A.rank(),A.row_join(b).rank()]
    out={'arity':5,'status':'exact rational curve span','ranks':ranks,'common_denominator':str(S.factor(D)),
         'curves':list(map(str,curves)),'target':str(target),'representatives':fam,'seconds':time.monotonic()-start}
    if ranks[0]==ranks[1]:
        sol,params=A.gauss_jordan_solve(b);sol=sol.subs({p:0 for p in params});assert S.cancel(sum(c*f for c,f in zip(sol,curves))-target)==0
        out['target_combination']=list(map(str,sol));out['status']='ENTIRE_PAIRED_RESIDUE_CURVE_CANNOT_SEPARATE_STARS'
    else:
        out['annihilators']=[list(map(str,v)) for v in A.T.nullspace() if (v.T*b)[0]!=0]
        out['status']='EXACT_PAIRED_RESIDUE_CURVE_SEPARATOR_EXISTS'
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print('FINAL',out['status'],'ranks',ranks,'seconds',out['seconds'],flush=True)

if __name__=='__main__':main()
