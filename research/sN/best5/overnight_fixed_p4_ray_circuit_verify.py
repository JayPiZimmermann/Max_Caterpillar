"""Solver-free independent replay of a closed triangle-facet proof.

The verifier does not trust producer circuit enumeration, branch selection,
LP status, or numerical coefficients. It verifies real circuit dependence,
all three closed facets, exact ray restrictions, and every rational leaf.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json,hashlib,time
import overnight_root9_equations as E
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();pp=HERE/'overnight_fixed_p4_ray_circuit.json';proof=json.loads(pp.read_text());assert proof['status']=='EXACT_CLOSED_TRIANGLE_PROOF'and proof['open_witness']is None;zs=proof['flats'];ds=proof['signs'];fans={r['flat']:r['rays']for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};forms=[E.arithmetic.flat(z)[0]for z in zs];values=[[[abs(sum(a*b for a,b in zip(f,r)))for f in fs]for r in fans[z]]for z,fs in zip(zs,forms)];local=[E.case_data((z,),(1,))[0]for z in zs];rows=[[[sum(c*v[j]for j,c in eq(i)[0].items())for v in vals]for i in range(49)]for vals,eq in zip(values,local)];rhs=[E.case_data(zs,ds)[0](i)[1]for i in range(49)];counts={'nodes':0,'branches':0,'leaves':0}
    def check(node,allowed):
        counts['nodes']+=1
        if node[0]=='cone':
            assert len(node)==2;co=[(i,Q(c))for i,c in node[1]];assert len({i for i,c in co})==len(co)and all(0<=i<49 for i,c in co);assert sum(c*rhs[i]for i,c in co)>0
            for k,js in enumerate(allowed):
                for j in js:assert ds[k]*sum(c*rows[k][i][j]for i,c in co)<=0
            counts['leaves']+=1;return
        assert node[0]=='triangle'and len(node)==7;k,inds,raw=node[1:4];assert 0<=k<4 and len(inds)==3 and len(set(inds))==3;cs=list(map(Q,raw));assert all(c>0 for c in cs);fs=[forms[k][j]for j in inds];assert any(all(sum(s*c*f[t]for s,c,f in zip(signs,cs,fs))==0 for t in range(len(fs[0])))for signs in product((1,-1),repeat=3))
        slacks=[[sum(c*v[j]for c,j in zip(cs,inds))-2*cs[t]*v[inds[t]]for t in range(3)]for v in values[k]];assert all(s>=0 for row in slacks for s in row);counts['branches']+=1
        for t in range(3):
            aa=list(allowed);aa[k]=tuple(j for j in allowed[k]if slacks[j][t]==0);check(node[4+t],tuple(aa))
    check(proof['tree'],tuple(tuple(range(len(fans[z])))for z in zs));assert counts==proof['counts'];out={'status':'INDEPENDENT_EXACT_TRIANGLE_FACET_PROOF_PASS','counts':counts,'flats':zs,'signs':ds,'seconds':time.monotonic()-start,'proof_sha256':hashlib.sha256(pp.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'One arbitrary-real K4 flat/sign case excluded, using complete ray fans and all closed triangle branches. No whole-domain lower bound.'};(HERE/'overnight_fixed_p4_ray_circuit_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__':main()
