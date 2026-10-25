"""Independent controls via the full head/hinge basis matrix, not rooted cuts.

A tree's head plus N−2 inner edge forms are a unimodular basis on x_7=0.
Dual coordinates lambda give lambda_0^(N−4)/prod_i lambda_i(lambda_i−lambda_0).
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,itertools,json,time
import numpy as np
import sympy as S
HERE=Path(__file__).parent

def direct(unit,point):
    rows=[]
    for u,v in [tuple(unit['roots'])]+list(map(tuple,unit['edges'])):
        rows.append([int(i==u)-int(i==v)for i in range(1,7)])
    A=S.Matrix(rows);det=int(A.det());assert abs(det)==1;B=A.T.inv();B=[[int(B[i,j])for j in range(6)]for i in range(6)];total=Q(0)
    for p in itertools.permutations(point):
        lam=[sum(row[i]*p[i]for i in range(6))for row in B];den=1
        for q in lam[1:]:den*=q*(q-lam[0])
        assert den;total+=Q(lam[0]**3,den)
    return total,det

def main():
    start=time.monotonic();source=HERE/'overnight_uniform_pruning_biforest.json';d=json.loads(source.read_text());text=(HERE/'overnight_uniform_pruning_signed7.txt').read_text().splitlines();points=[list(map(int,r.split()))for r in text[1:4]];matrix=np.fromfile(HERE/'overnight_uniform_pruning_biforest.u32',dtype='<u4').reshape(d['rows'],96);out=[]
    for j in(0,25,26,95):
        for i,p in enumerate(points):
            value,det=direct(d['new_units'][j],p);mod=value.numerator*pow(value.denominator,-1,d['prime'])%d['prime'];assert mod==int(matrix[i,j]);out.append({'unit':j,'point':i,'determinant':det,'exact_value':str(value)})
    result={'status':'INDEPENDENT_TWO_COMPONENT_BASIS_CONTROLS_PASS','comparisons':out,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'scope':'Independent exact arithmetic checks of12 evaluator entries. The rank129/130 result remains modular and is not an exact separator.'};Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(out),result['seconds'],flush=True)
if __name__=='__main__':main()
