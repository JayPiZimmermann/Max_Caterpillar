"""Controlled, bounded paired-normal Laurent DP gate at seven labels.

Checks the new epsilon^2 edge scaling against all exact five-label normal rows,
then evaluates all258 certified matching-deficient seven-label columns. Modular
rank is diagnostic only; a positive gap needs a later exact rational certificate.
Budget120seconds per phase, one thread, deterministic seed20261025.
"""
from pathlib import Path
from fractions import Fraction
import itertools,json,random,subprocess,time,hashlib
import numpy as np
from overnight_lower_dp import Compiler

HERE=Path(__file__).parent;P=1000003;ENGINE='/tmp/overnight_uniform_paired_engine'

def evaluate(dag,points,name,cols):
    txt=HERE/(name+'.txt');out=HERE/(name+'.u32');log=HERE/(name+'.engine.log')
    with txt.open('w') as f:
        f.write(f'{len(points)} {len(points[0][0])}\n')
        for b,d in points:f.write(' '.join(map(str,b+d))+'\n')
    before=time.monotonic()
    with log.open('w') as f:subprocess.run([ENGINE,str(dag),str(txt),str(out)],stderr=f,check=True,timeout=100)
    A=np.fromfile(out,dtype=np.uint32).reshape(len(points),cols+1)
    return A,time.monotonic()-before

def rank(rows):
    piv={}
    for row in rows:
        v=row.astype(np.int64).copy()
        for j,b in sorted(piv.items()):
            if v[j]:v=(v-v[j]*b)%P
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);piv[j]=v*pow(int(v[j]),P-2,P)%P
    return len(piv)

def main():
    start=time.monotonic();five=json.loads((HERE/'overnight_uniform_pair_normal.json').read_text())
    units=five['representatives'];dag5=Compiler(5).compile(units);path5=HERE/'overnight_uniform_paired_dp_5.bin';dag5.save(path5)
    points5=[([0,1,-1,p['z'],-p['z']],[-2*(1+p['q']),1,1,p['q'],p['q']]) for p in five['points']]
    got,t5=evaluate(path5,points5,'overnight_uniform_paired_dp_5',len(units))
    wanted=np.array([[Fraction(v).numerator*pow(Fraction(v).denominator,-1,P)%P for v in row] for row in five['rows']],dtype=np.uint32)
    assert np.array_equal(got,wanted)
    print('CONTROL5 all',len(points5),'rows',len(units),'columns PASS',t5,flush=True)
    rng=random.Random(20261025);points=[];seen=set()
    while len(points)<180:
        z2=rng.randrange(3,16);z3=rng.randrange(3*(1+z2)+1,150);p2=rng.randrange(1,16);p3=rng.randrange(1,16)
        key=(z2,z3,p2,p3)
        if key in seen:continue
        seen.add(key);points.append(([0,1,-1,z2,-z2,z3,-z3],[-2*(1+p2+p3),1,1,p2,p2,p3,p3]))
    rows,t7=evaluate(HERE/'overnight_lower_dp_7.bin',points,'overnight_uniform_paired_dp_7',258)
    ranks=[rank(rows[:,:-1]),rank(rows)]
    result={'status':'MODULAR_PAIRED_NORMAL_DIAGNOSTIC','arity':7,'prime':P,'rows':len(points),'columns':258,
        'ranks':ranks,'points':[{'base':b,'normal':d} for b,d in points],'n5_exact_controls':len(points5)*len(units),
        'n5_seconds':t5,'n7_seconds':t7,'total_seconds':time.monotonic()-start,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'engine_sha256':hashlib.sha256((HERE/'overnight_uniform_paired_engine.cpp').read_bytes()).hexdigest()}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],ranks,t7,flush=True)

if __name__=='__main__':main()
