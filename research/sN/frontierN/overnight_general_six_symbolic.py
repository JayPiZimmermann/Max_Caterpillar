"""Bounded symbolic gate for a surviving six-row coefficient-sign profile.

Every row is normalized by positive scaling so its first coefficient is +/-1.
Symbolic null vectors are cleared of denominators, leaving polynomial identities
valid even on parameter degeneracies. Nonzero coefficient guard is exact support,
not a generic-rank assumption. SymPy Groebner output is diagnostic until supplied
with independently checked polynomial-combination certificates.
"""
from pathlib import Path
import json,sys,time
import sympy as S
from overnight_general_six_peeling import prep

def main():
    fi,pi=map(int,sys.argv[1:3]);start=time.monotonic()
    source=json.loads(Path(__file__).with_name('overnight_general_six_peeling.json').read_text())
    rec=next(r for r in source['completed'] if r['family_index']==fi)
    fam=rec['family'];profile=rec['survivors'][pi];signs=profile['signs'];rows=[];params=[]
    for j,(sup,sgn) in enumerate(zip(fam,signs)):
        r=[S.Integer(0)]*5;r[sup[0]]=S.Integer(sgn[0]);vs=tuple(S.Symbol('p%d_%d'%(j,k)) for k in range(1,len(sup)-1))
        params+=list(vs)
        for i,v in zip(sup[1:-1],vs):r[i]=v
        r[sup[-1]]=-sum(r);rows.append(r)
    ell=S.symbols('e0:5');z=S.Symbol('guard_inverse')
    _,flags=prep(fam);cells=set()
    for lead,eps,a in flags:
        active=sum(1<<j for j,k in enumerate(lead) if signs[j][k]*eps[j]>0);cells.add((active,a))
    kernels={};constraints=set();out={'family_index':fi,'profile_index':pi,'family':fam,'signs':signs,
        'rows':[[str(v) for v in r] for r in rows],'params':list(map(str,params)), 'status':'building exact polynomial necessities'}
    path=Path(__file__).with_name('overnight_general_six_symbolic_%d_%d.json'%(fi,pi))
    for active,a in sorted(cells):
        if active not in kernels:
            M=S.Matrix([rows[j] for j in range(6) if active>>j&1]) if active else S.zeros(0,5)
            basis=[]
            for v in M.nullspace():
                v=[S.cancel(t) for t in v];den=S.lcm([S.denom(t) for t in v]);basis.append([S.cancel(den*t) for t in v])
            kernels[active]=basis
        for v in kernels[active]:
            poly=S.expand(sum(v[i]*ell[i] for i in range(5))-v[a])
            if poly!=0:constraints.add(poly)
    coeffs={S.factor(v) for r in rows for v in r if v.free_symbols}
    guard=S.prod(coeffs); polys=sorted(constraints,key=str)
    out.update({'constraints':list(map(str,polys)),'guard':str(guard),'cell_count':len(cells),
                'seconds_before_groebner':time.monotonic()-start,'status':'exact necessities saved; Groebner running'})
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('polys',len(polys),'parameters',len(params),'cells',len(cells),'sec',time.monotonic()-start,flush=True)
    gb=S.groebner(polys,*(ell+tuple(params)),order='grevlex')
    out['unguarded_basis']=list(map(str,gb.polys));path.write_text(json.dumps(out,indent=2)+'\n')
    print('unguarded basis',len(gb.polys),[str(p.as_expr()) for p in gb.polys],flush=True)
    guarded=S.groebner(polys+[z*guard-1],*(ell+tuple(params)+(z,)),order='grevlex')
    out.update({'guarded_basis':[str(p.as_expr()) for p in guarded.polys],
                'excluded':list(guarded)==[S.Integer(1)],'seconds':time.monotonic()-start,
                'status':'SymPy exact symbolic diagnostic; polynomial-combination checker pending'})
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('guarded_excluded',out['excluded'],'basis_size',len(guarded.polys),'sec',out['seconds'],flush=True)

if __name__=='__main__':main()
