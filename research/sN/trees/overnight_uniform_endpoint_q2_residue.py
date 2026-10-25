#!/usr/bin/env python3
"""One bounded exact residue-dictionary gate for the36-term endpoint proposal.

The full9! label sum is included. A nonempty dictionary is not a disproof
of a rational identity: its fractions may still satisfy circuit relations.
"""
from collections import Counter
from itertools import permutations
from pathlib import Path
import hashlib,json,math,os,resource,sys,time
os.environ.setdefault('OPENBLAS_NUM_THREADS','1');os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np

HERE=Path(__file__).parent;SCALE=1<<20


def main(k):
    resource.setrlimit(resource.RLIMIT_AS,(3*2**30,3*2**30));started=time.monotonic()
    inv=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text())['units']
    proposal=json.loads((HERE/'overnight_uniform_endpoint_q2.json').read_text())['results'][1]['proposals'][0]
    relation={int(j):int(w)for j,w in proposal['integer_proposal'].items()}
    assert len(relation)==36 and not proposal['target_coefficient']
    # Ordinary cut C={0,...,k-1}; two separately balanced blocks at s=0.
    frequency=[];at=0
    for size,normal_sign in((k,1),(9-k,-1)):
        total=[0]*8;total[7]=normal_sign
        for _ in range(size-1):
            vector=[0]*8;vector[at]=1;at+=1;frequency.append(tuple(vector));total=[x-y for x,y in zip(total,vector)]
        frequency.append(tuple(total))
    assert at==7 and len(frequency)==9
    subset=[tuple(sum(frequency[v][i]for v in range(9)if mask>>v&1)for i in range(8))for mask in range(512)]
    forms=[];form_index={}
    def norm(v):
        g=math.gcd(*v)
        assert g
        if next(x for x in v if x)<0:g=-g
        p=tuple(x//g for x in v)
        if p not in form_index:form_index[p]=len(forms);forms.append(p)
        return form_index[p],g
    cache={};zero=np.zeros((9,512,2),dtype=np.uint8);apex_data={}
    for apex in range(9):
        if not any(frequency[apex][:7]):continue
        apex_data[apex]=norm(frequency[apex][:7])
        for mask in range(1,512):
            if mask>>apex&1:continue
            for sign in(-1,1):
                q=subset[mask];factors=(q,tuple(q[i]+sign*frequency[apex][i]for i in range(8)))
                denominator=[];scale=1;zeros=0
                for f in factors:
                    if any(f[:7]):j,g=norm(f[:7]);denominator.append(j);scale*=g
                    else:zeros+=1;scale*=f[7]
                assert zeros<=1
                cache[apex,mask,sign]=(tuple(denominator),scale,zeros)
                zero[apex,mask,(sign+1)//2]=zeros
    perms=np.array(list(permutations(range(9))),dtype=np.uint8);count=len(perms)
    maps=np.zeros((count,256),dtype=np.uint16)
    for mask in range(1,256):
        bit=mask&-mask;v=bit.bit_length()
        maps[:,mask]=maps[:,mask^bit]|(np.uint16(1)<<perms[:,v].astype(np.uint16))
    apex_column=perms[:,0]
    answer=Counter();terms=0;progress=[]
    for number,(index,weight)in enumerate(relation.items()):
        unit=inv[index];cuts=[(sum(1<<(v-1)for v in side),sign)for side,sign in unit['cuts']]
        multiplicities=np.zeros(count,dtype=np.uint8)
        for mask,sign in cuts:multiplicities+=zero[apex_column,maps[:,mask],(sign+1)//2]
        assert int(multiplicities.max())<=1
        selected=np.flatnonzero(multiplicities)
        for row in selected:
            apex=int(apex_column[row]);numerator,num_scale=apex_data[apex]
            denominator=[];scale=1
            for mask,sign in cuts:
                factors,multiplier,_=cache[apex,int(maps[row,mask]),sign]
                denominator.extend(factors);scale*=multiplier
            assert len(denominator)==13 and numerator in denominator
            denominator.remove(numerator)
            assert SCALE%abs(scale)==0
            answer[(numerator,*sorted(denominator))]+=weight*(-num_scale)**5*(SCALE//scale)
            terms+=1
        if (number+1)%6==0:
            receipt=dict(units=number+1,terms=terms,raw_records=len(answer),seconds=time.monotonic()-started)
            progress.append(receipt);print(json.dumps(receipt),flush=True)
    answer={key:c for key,c in answer.items()if c}
    out=dict(status='EXACT_RESIDUE_DICTIONARY_FOR_ENDPOINT_Q2_PROPOSAL',subset_size=k,
             relation=relation,proposal_score_pairing=proposal['exact_score_pairing'],
             full_permutation_terms=terms,linear_forms=len(forms),surviving_records=len(answer),
             dictionary_cancels=not answer,coefficient_common_scale=SCALE,progress=progress,
             seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='An empty dictionary proves this full ordinary-cut residue is zero. A nonempty dictionary requires additional exact circuit reduction; no Q2 refutation or proof is inferred.')
    prefix=HERE/f'overnight_uniform_endpoint_q2_residue_{k}'
    if len(answer)<=400000:
        fractions=dict(frequency_chart=frequency,linear_forms=forms,
                       records=[dict(numerator=key[0],denominator=key[1:],coefficient=c)for key,c in answer.items()],
                       numerator_power=4,coefficient_common_scale=SCALE)
        import gzip
        with gzip.open(str(prefix)+'.fractions.json.gz','wt')as f:json.dump(fractions,f,separators=(',',':'))
        out['fraction_cache']=prefix.name+'.fractions.json.gz'
    Path(str(prefix)+'.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in('relation','progress')},indent=2),flush=True)


if __name__=='__main__':main(int(sys.argv[1])if len(sys.argv)>1 else 4)
