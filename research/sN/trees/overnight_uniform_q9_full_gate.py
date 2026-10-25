"""One-core modular row-space gate on the exact kappa quotient, plus target.

Target score1/3024 is forced by the proved caterpillar identity if Q_* descends.
A failed finite gate still requires all-frequency verification of a relation.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
import json,resource,sys,time
import numpy as np
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import nmod_mat,ctx
HERE=Path(__file__).parent;P=1000003

def qmod(s):q=Q(s);return q.numerator*pow(q.denominator,-1,P)%P
def gate(R,cols,scores,relations=False):
    before=time.monotonic();M=nmod_mat(R[:,cols].tolist(),P);RR,rank=M.rref();row=np.array([scores[j]for j in cols],dtype=np.int64);piv=[];cursor=0
    for i in range(rank):
        while not RR[i,cursor]:cursor+=1
        piv.append(cursor);a=int(row[cursor]);cursor+=1
        if a:row=(row-a*np.array([int(RR[i,j])for j in range(len(cols))],dtype=np.int64))%P
    out={'rank':rank,'score_in_sampled_rowspan':not bool(np.any(row)),'seconds':time.monotonic()-before}
    if relations and np.any(row):
        bad=[]
        for j in np.flatnonzero(row):
            rel={cols[int(j)]:1}
            for i,k in enumerate(piv):
                v=-int(RR[i,int(j)])%P
                if v:rel[cols[k]]=v
            bad.append((len(rel),int(j),int(row[j]),rel))
        _,j,pairing,rel=min(bad);out.update(smallest_violated_sampled_relation={str(j):v for j,v in rel.items()},score_pairing_mod=pairing,support=len(rel))
    return out

def main():
    ctx.threads=1;start=time.monotonic();state=json.loads((HERE/'overnight_uniform_q9_rows_state.json').read_text());D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());C=json.loads((HERE/'overnight_uniform_q9_quotient.json').read_text());width=len(D['units'])+1;R=np.fromfile(HERE/state['matrix'],dtype='<u4').reshape(state['rows'],width);scores=[qmod(s)for s in D['scores']]+[qmod('1/3024')];cd=C['class_data'];cols=[c['representative']for c in cd if c['matching']<4]+[c['representative']for c in cd if c['matching']==4]+[width-1];assert len(cols)==5451
    priorpath=HERE/'overnight_uniform_q9_full_gate.json';prior=json.loads(priorpath.read_text())if priorpath.exists()else None;full=gate(R,cols,scores,False);stable=bool(prior and prior['full']['rank']==full['rank']and prior['rows']<state['rows']);out={'status':'MODULAR_N9_FULL_SCORE_GATE','prime':P,'rows':state['rows'],'exact_function_classes':5450,'target_score':'1/3024','full':full,'rank_stable_from_previous_gate':stable,'prior_rows':prior['rows']if prior else None,'prior_rank':prior['full']['rank']if prior else None,'scope':'This is a modular diagnostic on finite evaluations. Stability is evidence, not a rank upper-bound proof. Any refutation needs an independently verified rational identity.'};print('full',state['rows'],full,'stable',stable,flush=True)
    byshape=defaultdict(list);stars=[]
    for c in cd:
        E=tuple(map(tuple,c['underlying_edges']));byshape[E].append(c)
        deg={v:0 for v in range(1,9)}
        for a,b in E:deg[a]+=1;deg[b]+=1
        if max(deg.values())==7:stars.append(c['representative'])
    subsets=[]
    for E,cs in byshape.items():
        if cs[0]['matching']!=4:continue
        sub=[c['representative']for c in cs]+stars+[width-1];ans=gate(R,sub,scores,True);ans.update(underlying_edges=E,columns=len(sub));subsets.append(ans);print('shape+target',len(sub),{k:v for k,v in ans.items()if k not in('smallest_violated_sampled_relation','underlying_edges')},flush=True)
    combined=[c['representative']for c in cd if c['matching']==4]+stars+[width-1];both=gate(R,combined,scores,True);both['columns']=len(combined);print('all PM+stars+target',{k:v for k,v in both.items()if k!='smallest_violated_sampled_relation'},flush=True)
    out.update(pm_shape_with_stars_and_target=subsets,all_pm_with_stars_and_target=both,seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss);(HERE/f'overnight_uniform_q9_full_gate_{state["rows"]}.json').write_text(json.dumps(out,indent=2)+'\n');priorpath.write_text(json.dumps(out,indent=2)+'\n');print('DONE',out['seconds'],out['peak_rss_kib'],flush=True)
if __name__=='__main__':main()
