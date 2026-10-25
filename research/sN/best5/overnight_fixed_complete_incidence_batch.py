from pathlib import Path
import subprocess,json,time,os
start=time.monotonic();rows=[]
for i in range(3):
    mode=f'merge{i}';prefix='overnight_fixed_complete_incidence_'+mode
    with Path(prefix+'.log').open('w')as log:r=subprocess.run(['python3','overnight_fixed_complete_incidence_smt.py',mode,'30'],stdout=log,stderr=subprocess.STDOUT,timeout=40)
    report=json.loads(Path(prefix+'.json').read_text())if Path(prefix+'.json').exists()else{};row={'mode':mode,'exit_code':r.returncode,'status':report.get('status'),'seconds':report.get('seconds')};rows.append(row);print(row,flush=True)
out={'scope':'three whole-cone merged-incidence construction subfamilies, all coefficients real and unbounded','results':rows,'seconds':time.monotonic()-start};Path('overnight_fixed_complete_incidence_batch.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
