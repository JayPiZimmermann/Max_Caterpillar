"""Exact next-jet defect of the two-star leading-projection identity.

Symbolic normal-head computation at symmetric outlier frequencies. This is
one specified witness/structural control, not an additional large rank search.
"""
from pathlib import Path
import itertools,json,time
import sympy as S
from overnight_uniform_pruning_infinity import normal_factors

HERE=Path(__file__).parent

def coefficient(unit,r,s):
    fac=normal_factors(unit,5);total=1+r+s;base=[-total/2,-total/2,S.Integer(1),r,s];slope=[1,-1,0,0,0];terms=[]
    for p in itertools.permutations(range(5)):
        b=[base[i] for i in p];d=[slope[i] for i in p];degree_num=int(d[0]!=0);dd=0;den=1;ratios=[]
        for C,h in fac:
            q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
            for off in [h,h+1]:
                c=q0+off*b[0];t=q1+off*d[0]
                if t:dd+=1;den*=t;ratios.append(c/t)
                else:assert c!=0;den*=c
        gap=dd-degree_num;assert gap>=2
        if gap>4:continue
        R=sum(ratios);inv=[S.Integer(1),-R,(R*R+sum(x*x for x in ratios))/2]
        num=[-d[0],-b[0],S.Integer(0)] if d[0] else [-b[0],S.Integer(0),S.Integer(0)]
        order=4-gap;terms.append(sum(num[k]*inv[order-k] for k in range(order+1))/den)
    return S.factor(S.cancel(sum(terms)))

def main():
    start=time.monotonic();data=json.loads((HERE/'overnight_uniform_pruning_gate.json').read_text());r,s=S.symbols('r s');curves=[coefficient(data['units'][i],r,s) for i in [0,1]];target=-(1+r+s)**2/(4*r*s);defect=S.factor(S.cancel(curves[0]/72-curves[1]/48-target))
    assert defect!=0
    result={'status':'EXACT_NEXT_JET_BREAKS_LEADING_WITNESS','curves':list(map(str,curves)),'target':str(target),'defect':str(defect),'seconds':time.monotonic()-start,'scope':'The leading two-star combination fails at the next inverse coefficient.'}
    eps=S.Symbol('eps');result['zero_sum_limit']=str(S.limit(defect.subs(s,-1-r+eps),eps,0))
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
