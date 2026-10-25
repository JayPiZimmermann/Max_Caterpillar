"""Bounded adaptive exact ray-cone templates, stopping at first exact survivor."""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
from functools import lru_cache
import json,time,signal,math,hashlib
import numpy as np
from scipy.optimize import linprog
import exact_lp
import overnight_root9_equations as E
from overnight_fixed_k2_certify import certified_feasible

HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();fans={r['flat']:r['rays'] for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};flatids=sorted(fans);indices={z:i for i,z in enumerate(flatids)};rhs=[E.case_data((flatids[0],),(1,))[0](i)[1]for i in range(49)]
    @lru_cache(None)
    def block(z):
        local=E.arithmetic.flat(z)[0];absvals=[[abs(sum(a*b for a,b in zip(f,r)))for f in local]for r in fans[z]];eq=E.case_data((z,),(1,))[0];return [[sum(c*ray[j]for j,c in eq(i)[0].items())for ray in absvals]for i in range(49)]
    @lru_cache(None)
    def integer_block(z):
        b=block(z);den=math.lcm(*(v.denominator for row in b for v in row));return np.array([[int(v*den)for v in row]for row in b],dtype=np.int64)
    learned=[];allowed=[];proofpath=HERE/'overnight_fixed_p4_k4_raylearn_proofs.jsonl';survivorpath=HERE/'overnight_fixed_p4_k4_raylearn_survivor.json';counts={'checked':0,'template_skipped':0,'lp':0,'templates':0};status='INCOMPLETE_BUDGET';signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('600 second budget')));signal.alarm(600)
    def eligibility(t):
        den=math.lcm(*(v.denominator for i,v in t));co=[(i,int(v*den))for i,v in t];out=[]
        for z in flatids:
            mat=integer_block(z);bound=sum(abs(v)*int(np.max(np.abs(mat[i])))for i,v in co);assert bound<2**62
            result=sum((v*mat[i]for i,v in co),np.zeros(len(fans[z]),dtype=np.int64));out.append((bool(np.all(result<=0)),bool(np.all(result>=0))))
        return out
    try:
      with proofpath.open('w')as out:
       for record in map(json.loads,(HERE/'overnight_fixed_p4_k4_raytemplate_survivors.jsonl').read_text().splitlines()):
        zs=record['flats']
        for sc,ds in enumerate(product((1,-1),repeat=4)):
          if not(record['sign_mask']>>sc&1):continue
          counts['checked']+=1
          if any(all(bits[indices[z]][int(d<0)]for z,d in zip(zs,ds))for bits in allowed):counts['template_skipped']+=1;continue
          blocks=[block(z)for z in zs];rows=[[v*d for b,d in zip(blocks,ds)for v in b[i]]for i in range(49)];n=len(rows[0]);counts['lp']+=1
          EE=[(['e',i],[-rhs[i]]+rows[i])for i in range(49)];II=[(['y',j],[Q(0)]+[Q(j==k)for k in range(n)])for j in range(n)];feasible,proof=certified_feasible(EE,II,n)
          if feasible:
            r=linprog(np.zeros(n),A_eq=np.array(rows,float),b_eq=np.array(rhs,float),bounds=(0,None),method='highs');assert r.success,r.message;supp=[j for j,v in enumerate(r.x)if v>1e-9];sol=exact_lp.solve_eq([[-rhs[i]]+[rows[i][j]for j in supp]for i in range(49)],len(supp));assert sol is not None and all(v>=0 for v in sol);assert all(sum(v*rows[i][j]for j,v in zip(supp,sol))==rhs[i]for i in range(49));rec={'status':'EXACT_RAYCONE_RELAXATION_SURVIVOR','flats':zs,'signs':ds,'weights':[[j,str(v)]for j,v in zip(supp,sol)if v],'ray_counts':[len(fans[z])for z in zs],'scope':'Exact nonnegative mixture of ray vectors; not actual single-preactivation feasibility and not a network.'};survivorpath.write_text(json.dumps(rec,sort_keys=True,indent=2)+'\n');print('EXACT_SURVIVOR',rec,flush=True);status=rec['status'];raise StopIteration
          eqw={i:Q(c)for(typ,i),c in proof if typ=='e'};b=sum(c*rhs[i]for i,c in eqw.items());assert b>0;t=tuple((i,c/b)for i,c in sorted(eqw.items())if c);assert all(sum(c*rows[i][j]for i,c in t)<=0 for j in range(n));bits=eligibility(t);assert all(bits[indices[z]][int(d<0)]for z,d in zip(zs,ds));learned.append(t);allowed.append(bits);counts['templates']+=1;rec={'flats':zs,'signs':ds,'template':[[i,str(c)]for i,c in t]};out.write(json.dumps(rec,separators=(',',':'))+'\n');out.flush();print('LEARNED',counts,'seconds',time.monotonic()-start,flush=True)
       status='ALL_INITIAL_SURVIVORS_EXCLUDED'
    except (TimeoutError,StopIteration)as exc:print(type(exc).__name__,str(exc),flush=True)
    finally:signal.alarm(0)
    table={'templates':[[[i,str(c)]for i,c in t]for t in learned],'flats':flatids,'allowed':allowed};tp=HERE/'overnight_fixed_p4_k4_raylearn_data.json';tp.write_text(json.dumps(table,separators=(',',':'))+'\n');report={'status':status,'counts':counts,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'proof_sha256':hashlib.sha256(proofpath.read_bytes()).hexdigest(),'data_sha256':hashlib.sha256(tp.read_bytes()).hexdigest()};(HERE/'overnight_fixed_p4_k4_raylearn.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
