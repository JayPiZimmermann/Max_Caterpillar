"""Exact replay of the ray-cone survivor and a missing triangle disjunction."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json,math,hashlib,time
import overnight_root9_equations as E

HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();wpath=HERE/'overnight_fixed_p4_k4_raylearn_survivor.json';w=json.loads(wpath.read_text());fans={r['flat']:r['rays']for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};zs=w['flats'];ds=w['signs'];weights={j:Q(c)for j,c in w['weights']};assert all(c>=0 for c in weights.values());ys=[];roff=0;violations=[]
    for k,z in enumerate(zs):
        forms=E.arithmetic.flat(z)[0];rays=fans[z];y=[sum(weights.get(roff+j,Q(0))*abs(sum(a*b for a,b in zip(f,r)))for j,r in enumerate(rays))for f in forms];ys+=y;roff+=len(rays)
        for inds in combinations(range(len(forms)),3):
            rows=[forms[j]for j in inds];rr=E.arithmetic.rref(rows)
            if len(rr)!=2 or any(len(E.arithmetic.rref([rows[i],rows[j]]))<2 for i,j in combinations(range(3),2)):continue
            # Independent tiny determinant formula for the unique circuit.
            cols=next((p,q)for p,q in combinations(range(len(rows[0])),2)if rows[0][p]*rows[1][q]-rows[0][q]*rows[1][p])
            p,q=cols;c=[rows[1][p]*rows[2][q]-rows[1][q]*rows[2][p],rows[2][p]*rows[0][q]-rows[2][q]*rows[0][p],rows[0][p]*rows[1][q]-rows[0][q]*rows[1][p]];assert all(sum(c[j]*rows[j][t]for j in range(3))==0 for t in range(len(rows[0])))
            den=math.lcm(*(v.denominator for v in c));c=[int(v*den)for v in c];g=math.gcd(*c);c=[v//g for v in c];v=[abs(c[j])*y[inds[j]]for j in range(3)]
            if all(2*x<sum(v)for x in v):violations.append({'block':k,'flat':z,'forms':inds,'circuit':c,'absolute_values':list(map(str,v)),'strict_triangle_slacks':[str(sum(v)-2*x)for x in v]})
    assert roff==sum(w['ray_counts']);eq=E.case_data(zs,ds)[0]
    for i in range(49):
        row,rhs=eq(i);assert sum(c*ys[j]for j,c in row.items())==rhs
    assert violations;out={'status':'EXACT_RAY_CONVEXIFICATION_SURVIVOR_VERIFIED','equations_checked':49,'ray_weights':len(weights),'violated_exact_triangle_disjunctions':len(violations),'first_violations':violations[:12],'seconds':time.monotonic()-start,'witness_sha256':hashlib.sha256(wpath.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'The necessary linear ray-cone system is feasible. This particular witness cannot arise from one preactivation per flat: three linearly dependent real numbers force one weighted absolute value to equal the sum of the other two.'};(HERE/'overnight_fixed_p4_ray_survivor_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True,indent=2))
if __name__=='__main__':main()
