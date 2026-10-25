"""One-core 64-row evaluation/RREF benchmark before a full Q_* gate."""
from pathlib import Path
import json,resource,subprocess,sys,time
import numpy as np
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import nmod_mat
from dfs_review_fourier import points
HERE=Path(__file__).parent;BASE=Path(__file__).with_suffix('');P=1000003

def valid(pt):
    for i,a in enumerate(pt):
        if not a%P:return False
        f=[x for j,x in enumerate(pt)if j!=i];s=[0]*256
        for m in range(1,256):b=m&-m;s[m]=s[m^b]+f[b.bit_length()-1]
        if any(not(q%P)or not((q+a)%P)or not((q-a)%P)for q in s[1:-1]):return False
    return True

def main():
    start=time.monotonic();data=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());ps=[]
    for pt in points(9,200):
        if valid(pt):ps.append(pt)
        if len(ps)==64:break
    assert len(ps)==64;ptfile=BASE.with_suffix('.txt');ptfile.write_text('64 9\n'+'\n'.join(' '.join(map(str,p))for p in ps)+'\n');out=BASE.with_suffix('.u32');before=time.monotonic();subprocess.run(['/tmp/overnight_lower_dp_engine',str(HERE/'overnight_uniform_q9_inventory.bin'),str(ptfile),str(out)],check=True);evaluation=time.monotonic()-before;A=np.fromfile(out,dtype='<u4').reshape(64,len(data['units'])+1)
    timings=[]
    for count in(16,32,64):
        before=time.monotonic();M=nmod_mat(A[:count].tolist(),P);_,rank=M.rref();timings.append({'rows':count,'rank':rank,'seconds':time.monotonic()-before});print('rref',timings[-1],flush=True)
    result={'status':'FULL_N9_MODULAR_GATE_BENCHMARK','columns':len(data['units']),'rows':64,'evaluation_seconds':evaluation,'seconds_per_evaluation_row':evaluation/64,'rref':timings,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'seconds':time.monotonic()-start,'scope':'Resource estimate only, not score descent or separation.'};BASE.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
