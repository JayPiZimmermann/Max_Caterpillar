"""Append one bounded modular batch; never touch exact9 campaign paths."""
from pathlib import Path
import json,resource,subprocess,sys,time
import numpy as np
from dfs_review_fourier import points
from overnight_uniform_q9_benchmark import valid
HERE=Path(__file__).parent

def main(total):
    start=time.monotonic();statefile=HERE/'overnight_uniform_q9_rows_state.json';state=json.loads(statefile.read_text())if statefile.exists()else {'rows':576,'matrix':'overnight_uniform_q9_rows576.u32','points':'overnight_uniform_q9_points576.json'};old=state['rows'];assert old<total<=old+1024;D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());width=len(D['units'])+1;ps=[]
    for pt in points(9,total+200):
        if valid(pt):ps.append(pt)
        if len(ps)==total:break
    assert len(ps)==total;assert [list(p)for p in ps[:old]]==json.loads((HERE/state['points']).read_text());base=HERE/f'overnight_uniform_q9_batch_{old}_{total}';ptfile=base.with_suffix('.txt');ptfile.write_text(f'{total-old} 9\n'+'\n'.join(' '.join(map(str,p))for p in ps[old:])+'\n');out=base.with_suffix('.u32')
    if not out.exists()or out.stat().st_size!=(total-old)*width*4:subprocess.run(['/tmp/overnight_lower_dp_engine',str(HERE/'overnight_uniform_q9_inventory.bin'),str(ptfile),str(out)],check=True)
    matrix=HERE/f'overnight_uniform_q9_rows{total}.u32'
    with matrix.open('wb')as f:
        f.write((HERE/state['matrix']).read_bytes());f.write(out.read_bytes())
    pts=HERE/f'overnight_uniform_q9_points{total}.json';pts.write_text(json.dumps(ps)+'\n');result={'status':'MODULAR_ROWS_READY','rows':total,'matrix':matrix.name,'points':pts.name,'new_rows':total-old,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss};statefile.write_text(json.dumps(result,indent=2)+'\n');base.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
if __name__=='__main__':main(int(sys.argv[1]))
