"""Exact smallest gate for (leading pair infinity, complete pair-cut residue).

The target's cut residue is zero. This tests whether keeping that boundary
function, rather than only its first large-z coefficient, repairs the exact
leading-projection obstruction on all10 canonical5-label star orbits.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time
import sympy as S
from overnight_uniform_pruning_cut_residue import residue

HERE=Path(__file__).parent

def main():
    start=time.monotonic();old=json.loads((HERE/'overnight_uniform_pruning_gate.json').read_text());units=old['units'];rows=[[S.Rational(v) for v in r] for r in old['rows']];descriptions=[{'kind':'leading','xi':p} for p in old['points']]
    for r,z in [(2,7),(3,11),(4,13),(5,17),(7,19),(11,29)]:
        eta=[1,r,-1-r];base=[z,-z]+eta;normal=[Q(-1,2),Q(-1,2),0,0,1]
        rows.append([residue(u,base,normal)[0] for u in units]+[Q(0)]);descriptions.append({'kind':'full_cut_residue','eta':eta,'z':z})
    A=S.Matrix(rows);ranks=[A[:,:-1].rank(),A.rank()];result={'status':'EXACT_LEADING_PLUS_CUT_RESIDUE_GATE','ranks':ranks,'rows':[[str(v) for v in r] for r in rows],'descriptions':descriptions,'units':units,'scope':'Complete5-label star domain; no uniform matching assertion.'}
    if ranks[0]<ranks[1]:
        w=next(w for w in A[:,:-1].T.nullspace() if(w.T*A[:,-1])[0]);w/=(w.T*A[:,-1])[0];assert w.T*A[:,:-1]==S.zeros(1,len(units)) and(w.T*A[:,-1])[0]==1;result['weights']=list(map(str,w))
    else:
        c,pars=A[:,:-1].gauss_jordan_solve(A[:,-1]);result['finite_combination']=list(map(str,c.subs({p:0 for p in pars})))
    result['seconds']=time.monotonic()-start
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],ranks,result['seconds'],flush=True)
if __name__=='__main__':main()
