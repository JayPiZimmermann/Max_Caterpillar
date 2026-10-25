"""Independent all-frequency N5 relation closing the odd-J current ansatz.

Normalized heads, every label permutation, and a common polynomial denominator.
Uses exact FLINT multivariate rational polynomials, not the evaluation grid.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import itertools,json,math,time
from flint import fmpq,fmpq_mpoly_ctx

UNITS=[{'root':1,'edges':[(2,1),(3,1),(4,2)]},
       {'root':1,'edges':[(2,1),(3,1),(2,4)]},
       {'root':1,'edges':[(2,1),(1,3),(2,4)]},
       {'root':1,'edges':[(2,1),(3,2),(2,4)]}]
WEIGHTS=[-1,-2,3,2]

def cuts(unit):
    h=[-1,0,0,0,0];h[unit['root']]+=1;E=[tuple(sorted(e))for e in unit['edges']];adj=[set()for _ in range(5)]
    for u,v in unit['edges']:
        if u>v:h[u]+=1;h[v]-=1
        adj[u].add(v);adj[v].add(u)
    out=[]
    for u,v in E:
        C={u};todo=[u]
        for x in todo:
            for y in adj[x]:
                if {x,y}=={u,v}:continue
                if y not in C:C.add(y);todo.append(y)
        out.append((C,sum(h[x]for x in C)))
    return out

def verify(units,weights,target_weight=0):
    base=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(-1,-1,-1,-1)];terms=[];union=Counter()
    for U,w in zip(units,weights):
        F=cuts(U)
        for p in itertools.permutations(range(5)):
            om=[base[i]for i in p];a=om[0];den=Counter();coef=Q(w)
            for C,H in F:
                q=tuple(sum(om[v][i]for v in C)for i in range(4))
                for k in(H,H+1):
                    f=tuple(q[i]+k*a[i]for i in range(4));g=math.gcd(*f)
                    if next(v for v in f if v)<0:g=-g
                    den[tuple(v//g for v in f)]+=1;coef/=g
            union|=den;terms.append((coef,tuple(-v for v in a),den))
    if target_weight:
        den=Counter();coef=Q(target_weight)
        for f in base:
            g=math.gcd(*f)
            if next(v for v in f if v)<0:g=-g
            den[tuple(v//g for v in f)]+=1;coef/=g
        union|=den;terms.append((coef,None,den))
    ctx=fmpq_mpoly_ctx.get(('r','s','t'));x=ctx.gens()
    def lin(c):return ctx.constant(c[0])+sum(c[i+1]*x[i]for i in range(3))
    polynomials={c:lin(c)for c in union};D=ctx.constant(1)
    for c,k in union.items():D*=polynomials[c]**k
    num=ctx.constant(0);quotients={}
    for coeff,a,den in terms:
        key=tuple(sorted(den.items()))
        if key not in quotients:
            v=D
            for c,k in den.items():v=v/(polynomials[c]**k)
            quotients[key]=v
        num+=fmpq(coeff.numerator,coeff.denominator)*(lin(a)if a is not None else 1)*quotients[key]
    assert num.is_zero()
    return {'units':units,'weights':weights,'target_weight':target_weight,'terms':len(terms),'denominator_factors':len(union),'denominator_degree':int(D.total_degree()),'numerator_zero':True}

def main():
    start=time.monotonic();first=verify(UNITS,WEIGHTS);first['identity']='-F0-2F1+3F3+2F17=0 (indices in the saved 26-unit family)'
    units=[UNITS[1],{'root':1,'edges':[(2,1),(3,2),(4,2)]},UNITS[3],{'root':1,'edges':[(2,1),(2,3),(2,4)]},{'root':2,'edges':[(2,1),(3,2),(2,4)]}];second=verify(units,[12,-4,-3,-3,-3],360);second['identity']='360 R_max+12 F1-4 F16-3 F17-3 F18-3 F23=0'
    result={'status':'INDEPENDENT_EXACT_CURRENT_RELATION_PASS','identities':[first,second],'scope':'Exact rational-function identities in three free frequency ratios, extended homogeneously to every generic frequency. The second expresses the target modulo star kernels using the one path value forced to zero by every J-wedge-K current. No sampled rank assumption.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
