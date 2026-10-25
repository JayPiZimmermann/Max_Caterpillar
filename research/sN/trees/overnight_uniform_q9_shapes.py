"""Bounded PM-shape gates with reusable complete N9 modular rows.

Only one modular worker. All paths are separate from exact9. Observed column
proportionalities are explicitly sampled; none is called an analytic identity.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
import json,math,resource,subprocess,sys,time
import numpy as np
import networkx as nx
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import nmod_mat
from dfs_review_fourier import points
from overnight_uniform_q9_benchmark import valid
HERE=Path(__file__).parent;BASE=Path(__file__).with_suffix('');P=1000003

def qmod(s):
    q=Q(s);return q.numerator*pow(q.denominator,-1,P)%P
def shape(U):return tuple(sorted(tuple(sorted(e))for e in U['edges']))

def main():
    start=time.monotonic();D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());units=D['units'];scores=[qmod(s)for s in D['scores']];ps=[]
    for pt in points(9,900):
        if valid(pt):ps.append(pt)
        if len(ps)==576:break
    assert len(ps)==576;oldtext=(HERE/'overnight_uniform_q9_benchmark.txt').read_text().splitlines()[1:];assert oldtext==[' '.join(map(str,p))for p in ps[:64]]
    ptfile=HERE/'overnight_uniform_q9_batch1.txt';ptfile.write_text('512 9\n'+'\n'.join(' '.join(map(str,p))for p in ps[64:])+'\n');batch=HERE/'overnight_uniform_q9_batch1.u32'
    if not batch.exists()or batch.stat().st_size!=512*(len(units)+1)*4:subprocess.run(['/tmp/overnight_lower_dp_engine',str(HERE/'overnight_uniform_q9_inventory.bin'),str(ptfile),str(batch)],check=True)
    R=np.vstack([np.fromfile(HERE/'overnight_uniform_q9_benchmark.u32',dtype='<u4').reshape(64,len(units)+1),np.fromfile(batch,dtype='<u4').reshape(512,len(units)+1)]).astype(np.int64);R.astype('<u4').tofile(HERE/'overnight_uniform_q9_rows576.u32');(HERE/'overnight_uniform_q9_points576.json').write_text(json.dumps(ps)+'\n');print('576 rows ready',time.monotonic()-start,flush=True)
    groups={};reps=[];mapping=[];scales=[];zero=[];pair_fail=[]
    for j,v in enumerate(R[:,:-1].T):
        nz=np.flatnonzero(v)
        if not len(nz):zero.append(j);mapping.append(-1);scales.append(0);continue
        first=int(v[int(nz[0])]);inv=pow(first,-1,P);key=(v*inv%P).astype('<u4').tobytes()
        if key not in groups:groups[key]=(len(reps),first,j);reps.append(j)
        g,rf,rj=groups[key];scale=first*pow(rf,-1,P)%P;mapping.append(g);scales.append(scale)
        if scores[j]!=scale*scores[rj]%P:pair_fail.append([rj,j])
    (HERE/'overnight_uniform_q9_compression576.json').write_text(json.dumps({'status':'SAMPLED_576_ROW_PROPORTIONALITY_MAP','prime':P,'rows':576,'representatives':reps,'column_to_group':mapping,'column_scale_to_representative':scales,'zero_columns':zero,'score_incompatible_pairs':pair_fail,'scope':'This map is verified on these576 rows only, not an exact rational identity certificate.'},indent=2)+'\n');print('sampled groups',len(reps),'zero',len(zero),'score pair failures',len(pair_fail),flush=True)
    byshape=defaultdict(list)
    for j,U in enumerate(units):byshape[shape(U)].append(j)
    star=[j for E,js in byshape.items()if max(dict(nx.Graph(E).degree()).values())==7 for j in js];cases=[]
    for E,js in byshape.items():
        if len(nx.max_weight_matching(nx.Graph(E),maxcardinality=True))!=4:continue
        selected={}
        for j in js+star:
            if mapping[j]>=0:selected.setdefault(mapping[j],j)
        cases.append((len(selected),E,js,list(selected.values())))
    results=[];out={'status':'MODULAR_N9_PM_SHAPE_SCORE_GATES','prime':P,'rows':576,'raw_columns':len(units),'sampled_groups':len(reps),'cases':results}
    for _,E,raw,cols in sorted(cases):
        progress=[];RR=None
        for count in(192,384,576):
            before=time.monotonic();M=nmod_mat(R[:count,cols].tolist(),P);RR,rank=M.rref();progress.append({'rows':count,'rank':rank,'seconds':time.monotonic()-before})
        piv=[next(j for j in range(len(cols))if RR[i,j])for i in range(rank)];row=[scores[j]for j in cols]
        for i,j in enumerate(piv):
            a=row[j]
            if a:row=[(row[k]-a*int(RR[i,k]))%P for k in range(len(cols))]
        violations=[]
        for j,x in enumerate(row):
            if not x:continue
            rel={cols[j]:1}
            for i,k in enumerate(piv):
                v=-int(RR[i,j])%P
                if v:rel[cols[k]]=v
            violations.append((len(rel),j,x,rel))
        entry={'underlying_edges':E,'raw_shape_columns':len(raw),'columns_with_stars_after_sampled_grouping':len(cols),'rank_progress':progress,'score_in_sampled_rowspan':not violations,'rank_stable_between_384_and_576':progress[-1]['rank']==progress[-2]['rank']}
        if violations:
            _,j,x,rel=min(violations);entry['smallest_violated_sampled_relation']={str(i):int(v)for i,v in rel.items()};entry['score_pairing_mod']=int(x);entry['support']=len(rel)
        results.append(entry);out.update(seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss);BASE.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('shape',len(raw),'grouped',len(cols),'ranks',[x['rank']for x in progress],'compatible',not violations,'support',entry.get('support'),'seconds',out['seconds'],flush=True)
    out['scope']='Finite-field necessary gates. A failed stable gate supplies a candidate relation, which still needs exact all-frequency verification before refuting the score. A compatible subset does not imply global or uniform descent.';BASE.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
