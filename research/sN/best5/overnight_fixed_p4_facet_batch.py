"""Bounded closed-facet batch with global exact-template reuse.

300 seconds / 100 completed cases. Stop at the first exact survivor after
all available rank-two three-form facet splits; never call it a network.
Frozen input stage is not modified. Every completed proof is flushed.
"""
from fractions import Fraction as Q
from pathlib import Path
from functools import lru_cache
from itertools import product
import hashlib,json,time,signal,math
import numpy as np
from scipy.optimize import linprog
import exact_lp
import overnight_root9_equations as E
from overnight_fixed_k2_certify import certified_feasible
from overnight_fixed_p4_ray_circuit import circuits
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();fans={r['flat']:r['rays']for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};rhs=[E.case_data((min(fans),),(1,))[0](i)[1]for i in range(49)];templates=[];tindex={};elig={};counts={'cases_seen':0,'template_exclusions':0,'proved_cases':0,'nodes':0,'leaves':0,'branches':0};lastcase=None
    def addtemplate(t):
        t=tuple((i,Q(c))for i,c in t);b=sum(c*rhs[i]for i,c in t);assert b>0;t=tuple((i,c/b)for i,c in sorted(t)if c)
        if t not in tindex:tindex[t]=len(templates);templates.append(t)
        return tindex[t]
    for name in('overnight_fixed_p4_k4_raytemplates_data.json','overnight_fixed_p4_k4_raylearn_data.json'):
        for t in json.loads((HERE/name).read_text())['templates']:addtemplate(t)
    def collect(node):
        if node[0]=='cone':addtemplate(node[1])
        elif node[0]=='triangle':
            for child in node[4:]:collect(child)
    known=json.loads((HERE/'overnight_fixed_p4_ray_circuit.json').read_text());collect(known['tree']);initialtemplates=len(templates)
    @lru_cache(None)
    def block(z):
        forms=E.arithmetic.flat(z)[0];vals=[[abs(sum(a*b for a,b in zip(f,r)))for f in forms]for r in fans[z]];eq=E.case_data((z,),(1,))[0];rows=[[sum(c*v[j]for j,c in eq(i)[0].items())for v in vals]for i in range(49)];den=math.lcm(*(v.denominator for row in rows for v in row));imat=np.array([[int(v*den)for v in row]for row in rows],dtype=np.int64);return vals,rows,imat
    @lru_cache(None)
    def circuit_data(z):
        vals=block(z)[0];out=[]
        for inds,c in circuits(E.arithmetic.flat(z)[0]):
            slacks=[[sum(c[t]*v[inds[t]]for t in range(3))-2*c[j]*v[inds[j]]for j in range(3)]for v in vals];assert all(s>=0 for row in slacks for s in row);out.append((inds,c,slacks))
        return out
    def eligible(z,ti,d):
        key=z,ti
        if key not in elig:
            t=templates[ti];den=math.lcm(*(c.denominator for i,c in t));co=[(i,int(c*den))for i,c in t];mat=block(z)[2];bound=sum(abs(c)*int(np.max(np.abs(mat[i])))for i,c in co);assert bound<2**62;value=sum((c*mat[i]for i,c in co),np.zeros(len(fans[z]),dtype=np.int64));elig[key]=bool(np.all(value<=0)),bool(np.all(value>=0))
        return elig[key][int(d<0)]
    def dfs(zs,ds,allowed,localcounts,depth=0):
        nonlocal lastcase
        localcounts['nodes']+=1;counts['nodes']+=1
        if localcounts['nodes']>400:raise RuntimeError('per-case node budget')
        cols=[(k,j)for k,js in enumerate(allowed)for j in js];rows=[[ds[k]*block(zs[k])[1][i][j]for k,j in cols]for i in range(49)];n=len(cols)
        # Exact single-equation checks, then proposed general cone certificate.
        for i,b in enumerate(rhs):
            if b and all(v*b<=0 for v in rows[i]):
                localcounts['leaves']+=1;counts['leaves']+=1;return['cone',[[i,str(1/b)]]]
        EE=[(['e',i],[-rhs[i]]+rows[i])for i in range(49)];II=[(['y',j],[Q(0)]+[Q(j==k)for k in range(n)])for j in range(n)];feasible,proof=certified_feasible(EE,II,n)
        if not feasible:
            co={i:Q(c)for(typ,i),c in proof if typ=='e'};b=sum(c*rhs[i]for i,c in co.items());assert b>0;t=[(i,c/b)for i,c in sorted(co.items())if c];assert all(sum(c*rows[i][j]for i,c in t)<=0 for j in range(n));localcounts['leaves']+=1;counts['leaves']+=1;return['cone',[[i,str(c)]for i,c in t]]
        r=linprog(np.zeros(n),A_eq=np.array(rows,float),b_eq=np.array(rhs,float),bounds=(0,None),method='highs');assert r.success;supp=[j for j,v in enumerate(r.x)if v>1e-9];sol=exact_lp.solve_eq([[-rhs[i]]+[rows[i][j]for j in supp]for i in range(49)],len(supp));assert sol is not None and all(v>=0 for v in sol);assert all(sum(v*rows[i][j]for j,v in zip(supp,sol))==rhs[i]for i in range(49));weights={cols[j]:v for j,v in zip(supp,sol)if v};choices=[]
        for k,z in enumerate(zs):
            for ci,(inds,c,slacks)in enumerate(circuit_data(z)):
                deficits=[sum(weights.get((k,j),Q(0))*slacks[j][t]for j in allowed[k])for t in range(3)]
                if min(deficits)>0:
                    children=[tuple(j for j in allowed[k]if slacks[j][t]==0)for t in range(3)];choices.append((max(map(len,children)),sum(map(len,children)),k,ci,children))
        if not choices:
            lastcase={'flats':zs,'signs':ds,'allowed':allowed,'weights':[[k,j,str(v)]for(k,j),v in weights.items()],'depth':depth};raise ValueError('EXACT_TRIANGLE_RELAXATION_SURVIVOR')
        _,_,k,ci,children=min(choices);inds,c,_=circuit_data(zs[k])[ci];localcounts['branches']+=1;counts['branches']+=1;tree=['triangle',k,list(inds),[str(v)for v in c]]
        for child in children:
            aa=list(allowed);aa[k]=child;tree.append(dfs(zs,ds,tuple(aa),localcounts,depth+1))
        return tree
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('300 second budget')));signal.alarm(300);status='COMPLETE_INPUT_DOMAIN';outpath=HERE/'overnight_fixed_p4_facet_batch_proofs.jsonl'
    try:
      with outpath.open('w')as out:
       for rec in map(json.loads,(HERE/'overnight_fixed_p4_k4_rayverified_survivors.jsonl').read_text().splitlines()):
        zs=rec['flats']
        for si,ds in enumerate(product((1,-1),repeat=4)):
          if not(rec['sign_mask']>>si&1):continue
          counts['cases_seen']+=1
          ti=next((ti for ti in range(initialtemplates,len(templates))if all(eligible(z,ti,d)for z,d in zip(zs,ds))),None)
          if ti is None:ti=next((ti for ti in range(140,initialtemplates)if all(eligible(z,ti,d)for z,d in zip(zs,ds))),None)
          if ti is not None:counts['template_exclusions']+=1;continue
          lc={'nodes':0,'leaves':0,'branches':0};tree=dfs(zs,ds,tuple(tuple(range(len(fans[z])))for z in zs),lc);collect(tree);counts['proved_cases']+=1;out.write(json.dumps({'flats':zs,'signs':ds,'counts':lc,'tree':tree},separators=(',',':'))+'\n');out.flush();print('CASE',zs,ds,lc,'totals',counts,'templates',len(templates),'seconds',time.monotonic()-start,flush=True)
          if counts['proved_cases']>=100:raise RuntimeError('100 completed-case budget')
    except(TimeoutError,ValueError,RuntimeError)as exc:status=str(exc);print('STOP',status,flush=True)
    finally:signal.alarm(0)
    tp=HERE/'overnight_fixed_p4_facet_batch_templates.json';tp.write_text(json.dumps({'templates':[[[i,str(c)]for i,c in t]for t in templates]},separators=(',',':'))+'\n');out={'status':status,'counts':counts,'initial_templates':initialtemplates,'final_templates':len(templates),'open_witness':lastcase,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'proof_sha256':hashlib.sha256(outpath.read_bytes()).hexdigest(),'templates_sha256':hashlib.sha256(tp.read_bytes()).hexdigest(),'scope':'Bounded targeted proof batch. Only saved complete trees are exclusions; no whole-domain lower bound unless independent coverage replay closes every remaining case.'};(HERE/'overnight_fixed_p4_facet_batch.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='open_witness'},sort_keys=True),flush=True)
if __name__=='__main__':main()
