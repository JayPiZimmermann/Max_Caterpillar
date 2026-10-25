"""Durable exact absolute-form arrangement rays for every P4 vanishing flat."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,signal,time
import overnight_root9_equations as E
from overnight_fixed_p4_k4_raycone_probe import ray_kernel


def main():
    started=time.monotonic();E.initialize();here=Path(__file__).parent;path=here/'overnight_fixed_p4_flat_rays.jsonl';done={}
    if path.exists():
        for line in path.read_text().splitlines():
            rec=json.loads(line);assert rec['flat']not in done;done[rec['flat']]=rec
    total_subsets=sum(__import__('math').comb(len(E.arithmetic.flat(z)[0]),len(B)-1)for z,B in E.arithmetic.BASES.items());signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('600 second ray inventory')));signal.alarm(600);complete=True
    try:
        with path.open('a')as out:
            for z in sorted(E.arithmetic.BASES,key=lambda z:(len(E.arithmetic.BASES[z]),z)):
                if z in done:continue
                forms=E.arithmetic.flat(z)[0];d=len(E.arithmetic.BASES[z]);assert len(E.arithmetic.rref(forms))==d;rays=sorted({v for rows in combinations(forms,d-1)if(v:=ray_kernel(rows,d))is not None});rec={'flat':z,'dimension':d,'forms':len(forms),'rays':rays};assert rays;out.write(json.dumps(rec,separators=(',',':'))+'\n');out.flush();done[z]=rec
                if len(done)%10==0 or d>=6:print('FLATS',len(done),'last',z,'dim',d,'rays',len(rays),'seconds',time.monotonic()-started,flush=True)
    except TimeoutError:complete=False;print('BUDGET_STOP_CHECKPOINT_SAVED',flush=True)
    finally:signal.alarm(0)
    report={'status':'COMPLETE_EXACT_P4_FLAT_RAY_INVENTORY'if complete else'PARTIAL_EXACT_P4_FLAT_RAY_INVENTORY','completed_flats':len(done),'expected_flats':len(E.arithmetic.BASES),'total_enumerated_normal_subsets':total_subsets,'total_rays':sum(len(r['rays'])for r in done.values()),'maximum_flat_rays':max(len(r['rays'])for r in done.values()),'seconds':time.monotonic()-started,'data_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact generator inventory for a necessary convex cone; no network-width lower bound yet.'};(here/'overnight_fixed_p4_flat_rays.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
