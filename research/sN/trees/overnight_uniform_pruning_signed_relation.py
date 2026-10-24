"""Independent all-frequency check of the failed two-root sign assignment.

Use normalized heads and a common polynomial denominator; no Fourier-grid
producer, signed-extension routine, or rooted-cut evaluator is imported.
"""
from pathlib import Path
from collections import Counter,defaultdict
import itertools,json,math,time
import sympy as S
HERE=Path(__file__).parent

def factors(unit):
    E=[tuple(sorted(e)) for e in unit['edges']];adj={i:set() for i in range(1,5)}
    for u,v in E:adj[u].add(v);adj[v].add(u)
    h=[-1,0,0,0,0];h[unit['root']]+=1
    for u,v in unit['edges']:
        if u>v:h[u]+=1;h[v]-=1
    out=[]
    for u,v in E:
        C={u};todo=[u]
        for x in todo:
            for y in adj[x]:
                if {x,y}=={u,v}:continue
                if y not in C:C.add(y);todo.append(y)
        out.append((C,sum(h[x] for x in C)))
    return out

def main():
    start=time.monotonic();data=json.loads((HERE/'overnight_uniform_pruning_signed_gate.json').read_text());weights={3:-3,16:1};terms=[];union=Counter()
    base=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(-1,-1,-1,-1)]
    for i,w in weights.items():
        cuts=factors(data['units'][i])
        for p in itertools.permutations(range(5)):
            b=[base[j] for j in p];a=b[0];den=Counter();coef=w
            for C,H in cuts:
                q=tuple(sum(b[j][k] for j in C) for k in range(4))
                for off in(H,H+1):
                    f=tuple(q[k]+off*a[k] for k in range(4));g=math.gcd(*f);first=next(z for z in f if z)
                    if first<0:g=-g
                    f=tuple(z//g for z in f);coef=S.Rational(coef,g);den[f]+=1
            union|=den;terms.append((coef,tuple(-z for z in a),den))
    # Homogeneity lets x0=1. The other three coordinates remain indeterminates.
    x=S.symbols('r s t');lin=lambda c:S.Poly(c[0]+sum(c[k+1]*x[k] for k in range(3)),*x,domain=S.QQ)
    P={c:lin(c) for c in union};D=S.Poly(1,*x,domain=S.QQ)
    for c,k in union.items():D*=P[c]**k
    numerator=S.Poly(0,*x,domain=S.QQ)
    for coef,a,den in terms:
        v=D
        for c,k in den.items():
            for _ in range(k):v=v.exquo(P[c])
        numerator+=v*lin(a)*coef
    assert numerator.is_zero
    result={'status':'INDEPENDENT_EXACT_TWO_ROOT_SIGN_DESCENT_REFUTATION','identity':'F_(root1;2>1,3>2,4>2) = 3 F_(root1;2>1,1>3,2>4)','all_frequency_identity':True,'arity':5,'terms':len(terms),'common_denominator_degree':D.total_degree(),'common_denominator_factors':len(union),'scope':'The proposed Gamma gives 0 to the star and -1 to the path, so it does not descend to the actual symmetrized rational kernels. This refutes this particular signed-product assignment, not a general two-factor construction or the all-tree lower bound.','seconds':time.monotonic()-start}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
