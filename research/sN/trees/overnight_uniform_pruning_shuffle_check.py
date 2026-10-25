"""Exact controls for the Vandermonde shuffle operation and polarization gap."""
from pathlib import Path
import itertools,json,math,time
import sympy as S

def chamber_constant(n):
    gaps=S.symbols('g:'+str(n-1));pos=[0]+[sum(gaps[:i])for i in range(1,n)];delta=S.prod(pos[j]-pos[i]for i in range(n)for j in range(i+1,n));poly=S.Poly(delta,*gaps);out=S.Rational(0)
    for powers,c in poly.terms():
        out+=c*S.prod(S.Rational(math.factorial(k),(n-1-i)**(k+1))for i,k in enumerate(powers))/n
    return out

def main():
    start=time.monotonic();assert chamber_constant(2)==S.Rational(1,2);assert chamber_constant(4)==S.Rational(3,16);s,t=S.symbols('s t');x=(0,0,1,1);y=(0,1,0,1);v=[t*a+s*b for a,b in zip(x,y)];delta=S.prod(v[j]-v[i]for i in range(4)for j in range(i+1,4));assert S.expand(delta-s**2*t**2*(t**2-s**2))==0;coefficient=S.expand(delta**2).coeff(t,6).coeff(s,6);assert coefficient==-2
    out={'status':'EXACT_VANDERMONDE_OPERATION_CONTROLS_PASS','chamber_constants':{'2':str(chamber_constant(2)),'4':str(chamber_constant(4))},'polarization_points':[x,y],'mixed_coefficient':str(coefficient),'scope':'The cone-integral argument proves the single-count identity uniformly. The four-variable example rules out a generic constant-coefficient extraction of two independent Vandermonde projections from a diagonal product, not every operation on the special tree kernels.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
