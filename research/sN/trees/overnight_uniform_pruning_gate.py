"""Smallest exact separation gate for the new pair-at-infinity map.

All10 canonical5-label star orbits. Full S5 sum maps to rational functions of
three unconstrained remaining frequencies. This tests the entire proposed
first operator through a finite exact gate; no large generic rank run.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time
import sympy as S
from dfs_review_fourier import family
from overnight_uniform_pruning_infinity import orbit_boundary,contract,contamination

HERE=Path(__file__).parent

def evaluate(u,xi):
    n=len(xi)+2;C,_=contamination(u,n);v=Q(2*(-1)**n*C,math.prod(xi))
    for e in u['edges']:
        w,c=contract(u,e,n);v+=2*orbit_boundary(w,c,xi)
    return v

def main():
    start=time.monotonic();units=[{'root':u['root'],'edges':u['edges']} for u in family(5,'nopath')];pts=[];rows=[]
    for r,s in itertools.product(range(2,9),range(11,19)):
        xi=[1,r,s]
        try:row=[evaluate(u,xi) for u in units]
        except AssertionError:continue
        pts.append(xi);rows.append(row+[Q(-1,math.prod(xi))])
        if len(rows)==30:break
    A=S.Matrix(rows);ranks=[A[:,:-1].rank(),A.rank()];data={'status':'EXACT_PAIR_INFINITY_FINITE_GATE','arity':5,'units':units,'points':pts,'rows':[[str(x) for x in r] for r in rows],'ranks':ranks}
    if ranks[0]==ranks[1]:
        sol,pars=A[:,:-1].gauss_jordan_solve(A[:,-1]);sol=sol.subs({p:0 for p in pars});assert A[:,:-1]*sol==A[:,-1]
        data['target_combination']=list(map(str,sol));data['scope']='Target lies in the span on this finite grid; not yet an identity of rational functions.'
    else:
        v=next(v for v in A[:,:-1].T.nullspace() if (v.T*A[:,-1])[0]);v/= (v.T*A[:,-1])[0];assert v.T*A[:,:-1]==S.zeros(1,len(units))
        data['weights']=list(map(str,v));data['scope']='Exact finite-evaluation separator after the new linear operator; no uniform arity claim.'
    data['seconds']=time.monotonic()-start
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n');print(data['status'],ranks,data.get('target_combination','separator'),data['seconds'],flush=True)
if __name__=='__main__':main()
