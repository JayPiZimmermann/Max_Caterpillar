"""Bounded nine-label paired Laurent-jet diagnostic, never a Q certificate.

Arity9, all3,822 matching-deficient rooted/oriented full orbit sums. Prime1000003.
One thread. Requested initial100 points, max exponent3, phase budget300seconds.
Generic paired base uses superincreasing positive coordinates; positive pair
normal values avoid a path contained in any pole. Coefficients satisfy parity.
"""
from pathlib import Path
import hashlib,json,random,subprocess,sys,time
import numpy as np
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages').resolve()))
from flint import nmod_mat
HERE=Path(__file__).parent;P=1000003
count=int(sys.argv[1]) if len(sys.argv)>1 else 100
start=time.monotonic();rng=random.Random(202610251);points=[]
while len(points)<count:
    z2=rng.randrange(3,15);z3=rng.randrange(3*(1+z2)+1,120);z4=rng.randrange(3*(1+z2+z3)+1,1200)
    p2,p3,p4=[rng.randrange(1,18) for _ in range(3)]
    points.append(([0,1,-1,z2,-z2,z3,-z3,z4,-z4],[-2*(1+p2+p3+p4),1,1,p2,p2,p3,p3,p4,p4]))
stem=f'overnight_uniform_jet9_{count}'
txt=HERE/(stem+'.txt');out=HERE/(stem+'.u32');log=HERE/(stem+'.engine.log')
with txt.open('w') as f:
    f.write(f'{count} 9\n')
    for b,d in points:f.write(' '.join(map(str,b+d))+'\n')
with log.open('w') as f:subprocess.run(['/tmp/overnight_uniform_jet_engine',str(HERE/'overnight_lower_dp_9.bin'),str(txt),str(out),'3'],stderr=f,check=True,timeout=300)
eval_time=time.monotonic()-start
A=np.fromfile(out,dtype=np.uint32).reshape(count,18,3823)
assert not np.any(A[:,::2,:]),'parity failure'
active=[k for k in range(18) if np.any(A[:,k,:])]
rows=A[:,active,:].reshape(-1,3823)
def rank(B):return int(nmod_mat(B.shape[0],B.shape[1],list(map(int,B.ravel())),P).rank())
by={str(k-14):[rank(A[:,k,:-1]),rank(A[:,k,:])] for k in active}
ranks=[rank(rows[:,:-1]),rank(rows)]
result={'status':'MODULAR_N9_PAIRED_JET_DIAGNOSTIC','arity':9,'prime':P,'point_count':count,'max_exponent':3,'columns':3822,'active_rows':len(rows),'ranks':ranks,'ranks_by_exponent':by,'evaluation_seconds':eval_time,'total_seconds':time.monotonic()-start,'parity_control':True,'engine_sha256':hashlib.sha256((HERE/'overnight_uniform_jet_engine.cpp').read_bytes()).hexdigest(),'point_sha256':hashlib.sha256(txt.read_bytes()).hexdigest()}
(HERE/(stem+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
