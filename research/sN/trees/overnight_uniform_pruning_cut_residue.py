"""All-remaining-label cut residues, retaining both large-apex placements.

Independent direct normalized-head residues for the two5-label star witnesses;
exact7-label control of the all-outward continuation formula. No rank search.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time
import sympy as S
from overnight_uniform_pruning_infinity import normal_factors

HERE=Path(__file__).parent

def residue(unit,base,normal,symbolic=False):
    n=len(base);fac=normal_factors(unit,n);terms=[];counts={0:0,1:0}
    for p in itertools.permutations(range(n)):
        b=[base[i] for i in p];d=[normal[i] for i in p];zeros=[];den=1
        for C,h in fac:
            q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
            for off in [h,h+1]:
                c=q0+off*b[0];t=q1+off*d[0]
                if symbolic:c=S.expand(c)
                if c==0:assert t;zeros.append(t)
                else:den*=c
        assert len(zeros)<=1
        if zeros:
            counts[int(p[0]<2)]+=1
            terms.append((-b[0])**(n-4)/(zeros[0]*den) if symbolic else Q((-b[0])**(n-4),zeros[0]*den))
    return S.factor(S.cancel(sum(terms))) if symbolic else sum(terms),counts

def main():
    start=time.monotonic();r,z=S.symbols('r z');source=json.loads((HERE/'overnight_uniform_pruning_gate.json').read_text());base=[z,-z,S.Integer(1),r,-1-r];normal=[S.Rational(-1,2),S.Rational(-1,2),0,0,1];curves=[];counts=[]
    for u in source['units'][:2]:
        f,c=residue(u,base,normal,True);curves.append(f);counts.append(c)
    D=(z*z-1)*(z*z-r*r)*(z*z-(1+r)**2);p2=1+r*r+(1+r)**2
    assert S.cancel(curves[0]-12*p2/D)==0
    assert S.cancel(curves[1]-(-48*z*z+8*p2)/D)==0
    assert S.cancel(curves[0]/72-curves[1]/48-z*z/D)==0
    # Same source orientation as U0: root leaf1, centre2, root-to-centre,
    # then every other leaf positive. There are d=5 nonapex leaves.
    u7={'root':1,'edges':[(2,1)]+[(j,2) for j in range(3,7)]};eta=[1,3,9,27,-40];zz=127
    measured,c7=residue(u7,[zz,-zz]+eta,[Q(-1,2),Q(-1,2)]+[0]*4+[1])
    d=len(eta);e={k:sum(math.prod(c) for c in itertools.combinations(eta,k)) for k in range(d+1)}
    proposed=Q(2*math.factorial(d)*sum(x*x for x in eta)*zz**(d-3)*sum(e[k]*zz**(d-k) for k in range(3,d+1,2)),math.prod(eta)*math.prod(zz*zz-x*x for x in eta))
    assert measured==proposed
    result={'status':'EXACT_FULL_CUT_RESIDUE_CONTROLS_PASS','five_label_curves':list(map(str,curves)),'five_label_assignment_counts':counts,'witness_residue':'z^2 / product_(eta in [1,r,-1-r]) (z^2-eta^2)','seven_label_star_value':str(measured),'seven_label_assignment_counts':c7,'seconds':time.monotonic()-start,'scope':'Exact cut-residue identities and a uniform-star formula control; no uniform all-tree separator.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
