"""All paired principal parts and first positive jet, bounded modular gate."""
from pathlib import Path
import hashlib,json,subprocess,time
import numpy as np
from overnight_uniform_paired_dp import rank
HERE=Path(__file__).parent
ENGINE='/tmp/overnight_uniform_jet_engine'
start=time.monotonic();results={}
for n,cols in [(5,10),(7,258)]:
    stem=f'overnight_uniform_jet_{n}'
    dag=HERE/('overnight_uniform_paired_dp_5.bin' if n==5 else 'overnight_lower_dp_7.bin')
    txt=HERE/f'overnight_uniform_paired_dp_{n}.txt'
    out=HERE/(stem+'.u32');log=HERE/(stem+'.engine.log')
    with log.open('w') as f: subprocess.run([ENGINE,str(dag),str(txt),str(out),'1'],stderr=f,check=True,timeout=100)
    count=int(txt.read_text().split()[0]);d=2*n-3
    A=np.fromfile(out,dtype=np.uint32).reshape(count,d+1,cols+1)
    old=np.fromfile(HERE/f'overnight_uniform_paired_dp_{n}.u32',dtype=np.uint32).reshape(count,cols+1)
    assert np.array_equal(A[:,-3,:],old)
    assert not np.any(A[:,::2,:]), 'oddness check failed'
    by_exponent={str(k-2*n+4):[rank(A[:,k,:-1]),rank(A[:,k,:])] for k in range(d+1) if np.any(A[:,k,:])}
    flat=A.reshape(-1,cols+1)
    ranks=[rank(flat[:,:-1]),rank(flat)]
    results[str(n)]={'columns':cols,'points':count,'coefficient_rows':count*(d+1),'ranks':ranks,'ranks_by_exponent':by_exponent,'oddness_control':True,'first_residue_control':True}
    print(n,results[str(n)],flush=True)
result={'status':'MODULAR_FIRST_POSITIVE_JET_DIAGNOSTIC','prime':1000003,'results':results,'seconds':time.monotonic()-start,'engine_sha256':hashlib.sha256((HERE/'overnight_uniform_jet_engine.cpp').read_bytes()).hexdigest()}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
