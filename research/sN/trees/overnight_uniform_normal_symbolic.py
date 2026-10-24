"""Symbolic normal-dependent paired residue at five labels, exact over Q(z,r).
Extract a small coefficient functional and look for a uniform matching invariant.
Budget120seconds, one thread; no all-arity conclusion from this finite gate.
"""
from pathlib import Path
import itertools,json,time
import sympy as S
from dfs_review_fourier import family
from overnight_uniform_pair_residue_check import factors

def main():
    start=time.monotonic();z,r=S.symbols('z r');base=[S.Integer(0),S.Integer(1),S.Integer(-1),z,-z];normal=[-2*(1+r),S.Integer(1),S.Integer(1),r,r]
    fam=family(5,'nopath');curves=[]
    for index,u in enumerate(fam):
        terms=[]
        for perm in itertools.permutations(range(5)):
            b=[base[i] for i in perm];d=[normal[i] for i in perm];nonzero=[];zero=[]
            for C,h in factors(u):
                q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
                for offset in [h,h+1]:
                    c=q0+offset*b[0];t=q1+offset*d[0]
                    if c==0:assert t!=0;zero.append(t)
                    else:nonzero.append((c,t))
            assert len(zero)<=2
            if not zero:continue
            den=S.prod(zero)*S.prod(c for c,t in nonzero);numerator=-b[0]
            if len(zero)==2:numerator=-d[0]+b[0]*sum(t/c for c,t in nonzero)
            terms.append(numerator/den)
        f=S.factor(S.cancel(sum(terms)));curves.append(f)
        print('column',index,'curve',f,'seconds',time.monotonic()-start,flush=True)
    target=-S.Rational(1,2)/(1+r)/z**2;D=S.lcm([S.denom(S.cancel(f)) for f in curves+[target]])
    polys=[S.Poly(S.cancel(D*f),z,r) for f in curves+[target]]
    monomials=sorted(set().union(*(set(p.monoms()) for p in polys)))
    A=S.Matrix([[p.coeff_monomial(m) for p in polys[:-1]] for m in monomials]);b=S.Matrix([polys[-1].coeff_monomial(m) for m in monomials])
    ranks=[A.rank(),A.row_join(b).rank()];null=[v for v in A.T.nullspace() if (v.T*b)[0]!=0]
    v=min(null,key=lambda v:sum(c!=0 for c in v));v=v/(v.T*b)[0]
    assert v.T*A==S.zeros(1,len(fam)) and (v.T*b)[0]==1
    out={'status':'EXACT_SYMBOLIC_FIVE_LABEL_NORMAL_RESIDUE_SEPARATOR','ranks':ranks,'denominator':str(S.factor(D)),
         'monomials_z_r':monomials,'curves':list(map(str,curves)),'target':str(target),'coefficient_weights':list(map(str,v)),
         'representatives':fam,'seconds':time.monotonic()-start}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DENOM',S.factor(D),'RANKS',ranks,'FUNCTIONAL',[(m,c) for m,c in zip(monomials,v) if c],flush=True)

if __name__=='__main__':main()
