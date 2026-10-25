#!/usr/bin/env python3
"""Endpoint-only necessary gate for the unchanged Q2 formula.

Reuses existing N7/N9 frequency rows; generates no new evaluations.
Any failed sampled relation still requires exact rational certification.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,math,os,resource,sys,time
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import nmod_mat,ctx
from overnight_uniform_fay import KEYS,vec
from overnight_uniform_fay_q2_verify import COEFF,target_formula
from overnight_root_q2_full_gate import reconstruct

HERE=Path(__file__).parent;P=1000003


def endpoint(u):return all(sign==1 or len(side)==1 for side,sign in u['cuts'])


def gate(N,units,cols,matrix,target_index):
    started=time.monotonic();columns=cols+[target_index]
    values=np.asarray(matrix[:,columns],dtype=np.uint32)
    R,rank=nmod_mat(values.tolist(),P).rref()
    weights=[COEFF.get(key,Q(0))for key in KEYS]
    scores=[sum(w*int(v)for w,v in zip(weights,vec(units[j])))for j in cols]
    scores.append(target_formula((N-1)//2)/math.factorial(N))
    remaining=np.array([v.numerator*pow(v.denominator,-1,P)%P for v in scores],dtype=np.int64)
    pivots=[];cursor=0
    for i in range(rank):
        while not R[i,cursor]:cursor+=1
        pivots.append(cursor)
        coefficient=int(remaining[cursor]);cursor+=1
        if coefficient:remaining=(remaining-coefficient*np.array([int(R[i,j])for j in range(len(columns))],dtype=np.int64))%P
    violations=[]
    for j in np.flatnonzero(remaining):
        relation={int(j):1}
        for i,k in enumerate(pivots):
            coefficient=-int(R[i,int(j)])%P
            if coefficient:relation[k]=coefficient
        violations.append((len(relation),int(j),relation))
    proposals=[]
    for support,j,relation in sorted(violations,key=lambda r:r[:2])[:12]:
        rational={k:reconstruct(v)for k,v in relation.items()}
        item=dict(support=support,pairing_mod=int(remaining[j]))
        if all(v is not None for v in rational.values()):
            scale=math.lcm(*(v.denominator for v in rational.values()))
            item['integer_proposal']={columns[k]:int(v*scale)for k,v in rational.items()}
            item['exact_score_pairing']=str(sum(int(v*scale)*scores[k]for k,v in rational.items()))
            item['target_coefficient']=item['integer_proposal'].get(target_index,0)
        else:item['relation_mod']={columns[k]:v for k,v in relation.items()}
        proposals.append(item)
    return dict(arity=N,rows=matrix.shape[0],endpoint_columns=len(cols),rank=rank,
                nonzero_unit_scores=sum(v!=0 for v in scores[:-1]),target_score=str(scores[-1]),
                score_in_sampled_rowspan=not violations,violated_sampled_relations=len(violations),
                endpoint_indices=cols,exact_scores=list(map(str,scores)),proposals=proposals,
                seconds=time.monotonic()-started)


def main():
    ctx.threads=1;resource.setrlimit(resource.RLIMIT_AS,(3*2**30,3*2**30));started=time.monotonic();results=[]
    d7=json.loads((HERE/'overnight_uniform_pruning_signed7.json').read_text());units7=d7['units']
    rows7=np.memmap(HERE/'overnight_uniform_pruning_signed7.u32',dtype='<u4',mode='r',shape=(d7['rows'],len(units7)+1))
    results.append(gate(7,units7,[j for j,u in enumerate(units7)if endpoint(u)],rows7,len(units7)))
    print(json.dumps({k:v for k,v in results[-1].items()if k not in('endpoint_indices','exact_scores','proposals')},indent=2),flush=True)
    inv=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());units9=inv['units']
    classes=json.loads((HERE/'overnight_uniform_q9_quotient.json').read_text())['class_data']
    cols=[c['representative']for c in classes if endpoint(units9[c['representative']])]
    state=json.loads((HERE/'overnight_uniform_q9_rows_state.json').read_text());old=state['rows'];width=len(units9)+1
    oldrows=np.memmap(HERE/state['matrix'],dtype='<u4',mode='r',shape=(old,width))
    newrows=np.memmap(HERE/'overnight_root_q2_full_gate_3400.u32',dtype='<u4',mode='r',shape=(3400-old,width))
    # Only selected columns are copied; immutable full caches stay memory-mapped.
    selected=cols+[width-1]
    compact=np.concatenate((oldrows[:,selected],newrows[:,selected]),axis=0)
    compact_units=[units9[j]for j in cols]
    result=gate(9,compact_units,list(range(len(cols))),compact,len(cols))
    mapping=cols+[width-1]
    result['endpoint_indices']=cols
    for proposal in result['proposals']:
        for key in('integer_proposal','relation_mod'):
            if key in proposal:proposal[key]={mapping[j]:v for j,v in proposal[key].items()}
    results.append(result)
    print(json.dumps({k:v for k,v in result.items()if k not in('endpoint_indices','exact_scores','proposals')},indent=2),flush=True)
    out=dict(status='NECESSARY_ENDPOINT_ONLY_Q2_GATE_ON_EXISTING_ROWS',prime=P,results=results,
             seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='The Q2 formula is unchanged. No new frequency generation, exact rational rank, or relation identity is claimed. Any failed proposal needs a generic-Fourier identity check, not necessarily a whole-function identity.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print('proposal sizes',[[p['support']for p in r['proposals']]for r in results],flush=True)


if __name__=='__main__':main()
