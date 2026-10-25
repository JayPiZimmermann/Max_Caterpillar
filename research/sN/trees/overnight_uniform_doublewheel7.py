#!/usr/bin/env python3
"""Bounded N7 diagnostic for the actual double-wheel residue map.

Exact preprocessing creates a common rational fraction-product dictionary.
Finite-field ranks remain diagnostic unless a resulting relation is checked
as an identity in that dictionary or by a separate rational identity gate.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib
import json
import math
import random
import time
import numpy as np

HERE=Path(__file__).parent
PRIME=1000003


def add(x,y,scale=1):return tuple(a+scale*b for a,b in zip(x,y))


def rank_rows(rows):
    basis={}
    for row in rows:
        v=np.array(row,dtype=np.int64)%PRIME
        for j,b in sorted(basis.items()):v=(v-v[j]*b)%PRIME
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);basis[j]=v*pow(int(v[j]),PRIME-2,PRIME)%PRIME
    return len(basis),sorted(basis)


def main():
    started=time.monotonic()
    source=HERE/'overnight_lower_matching_rows_7.json'
    domain=json.loads(source.read_text())
    ids=[]
    for j,u in enumerate(domain['representatives']):
        degree=Counter(v for e in u['edges']for v in e)
        hubs=Counter(v for leaf,v in u['edges']if leaf!=u['root']and degree[leaf]==1)
        if max(hubs.values(),default=0)>=2:ids.append(j)
    assert len(ids)==92
    old_rows=[[row[j]for j in ids]for row in domain['modular_rows']]
    old_rank,old_pivots=rank_rows(old_rows)
    assert old_rank==47

    # At s=t=0 use four independent outside frequencies x0,...,x3 and
    # a=x0+...+x3. The final outside frequency absorbs -s-t off the stratum.
    frequency=[(1,1,1,1,0,0),(-1,-1,-1,-1,1,0),(-1,-1,-1,-1,0,1),
               (1,0,0,0,0,0),(0,1,0,0,0,0),(0,0,1,0,0,0),(0,0,0,1,-1,-1)]
    subset=[]
    for mask in range(1<<7):
        value=(0,)*6
        for v in range(7):
            if mask>>v&1:value=add(value,frequency[v])
        subset.append(value)
    linear_forms=[]
    linear_index={}
    def normalize(form):
        divisor=math.gcd(*form)
        assert divisor
        if next(v for v in form if v)<0:divisor=-divisor
        primitive=tuple(v//divisor for v in form)
        if primitive not in linear_index:
            linear_index[primitive]=len(linear_forms);linear_forms.append(primitive)
        return linear_index[primitive],divisor
    edges={}
    for apex in range(3):
        for mask in range(1,1<<7):
            if mask>>apex&1:continue
            for sign in(-1,1):
                forms=(subset[mask],add(subset[mask],frequency[apex],sign))
                regular=[];scale=1;zero=[]
                for form in forms:
                    if any(form[:4]):
                        index,multiplier=normalize(form[:4]);regular.append(index);scale*=multiplier
                    else:zero.append(form[4:])
                assert len(zero)<=1
                edges[(apex,mask,sign)]=(tuple(regular),scale,tuple(zero))

    maps=[]
    for p in permutations(range(7)):
        if p[0]>=3:continue
        mapped=[0]*64
        for mask in range(1,64):
            bit=mask&-mask;vertex=bit.bit_length()
            mapped[mask]=mapped[mask^bit]|(1<<p[vertex])
        maps.append((p[0],mapped))
    assert len(maps)==2160
    record_index={};records=[];columns=[]
    for position,index in enumerate(ids):
        unit=domain['representatives'][index]
        cuts=[(sum(1<<(v-1)for v in side),sign)for side,sign in unit['cuts']]
        entries=Counter()
        for apex,mapped in maps:
            regular=[];zero=[];scale=1
            for mask,sign in cuts:
                reg,mult,vanish=edges[(apex,mapped[mask],sign)]
                regular.extend(reg);scale*=mult;zero.extend(vanish)
            assert len(zero)<=2
            if len(zero)!=2:continue
            pure=[v for v in zero if v[1]==0]
            if not pure:continue
            assert len(pure)==1
            other=zero[1]if zero[0]==pure[0]else zero[0]
            scale*=pure[0][0]*other[1]
            assert scale and len(regular)==8
            key=tuple(sorted(regular))
            if key not in record_index:
                record_index[key]=len(records);records.append(key)
            # (-actual_apex)^3 = -a^3 at apex0 and +a^3 at apex1/2.
            entries[record_index[key]]+=Q(-1 if apex==0 else 1,scale)
        columns.append([(j,c.numerator,c.denominator)for j,c in sorted(entries.items())if c])
        if position%20==0:print('PREPROCESS',position+1,'/92',len(records),'fractions',round(time.monotonic()-started,3),flush=True)
    exact=dict(arity=7,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               original_column_indices=ids,linear_forms=linear_forms,fraction_denominators=records,
               columns=columns,numerator='(x0+x1+x2+x3)^3',
               scope='Exact common fraction-product representation of Res_t Res_s of each full symmetric outward-twin orbit.')
    artifact=HERE/'overnight_uniform_doublewheel7_fractions.json'
    artifact.write_text(json.dumps(exact,separators=(',',':'))+'\n')
    modular_columns=[[(j,num*pow(den,PRIME-2,PRIME)%PRIME)for j,num,den in column]for column in columns]
    rng=random.Random(271828)
    points=[];rows=[]
    for number in range(96):
        while True:
            point=tuple(rng.randrange(1,200)for _ in range(4))
            values=[sum(a*b for a,b in zip(form,point))%PRIME for form in linear_forms]
            if all(values):break
        inverses=[pow(v,PRIME-2,PRIME)for v in values]
        numerator=pow(sum(point),3,PRIME)
        fractions=[]
        for factors in records:
            value=numerator
            for j in factors:value=value*inverses[j]%PRIME
            fractions.append(value)
        row=[sum(fractions[j]*c for j,c in column)%PRIME for column in modular_columns]
        points.append(point);rows.append(row)
        if (number+1)%24==0:
            rank,_=rank_rows(rows)
            print('ROWS',number+1,'residue_rank',rank,'original_rank',old_rank,'seconds',round(time.monotonic()-started,3),flush=True)
    new_rank,new_pivots=rank_rows(rows)
    joint_rank,_=rank_rows(old_rows+rows)
    result=dict(status='MODULAR_DOUBLEWHEEL_INJECTIVITY_DIAGNOSTIC_ONLY',arity=7,
                literal_outward_twin_orbits=92,prime=PRIME,original_evaluation_rank=old_rank,
                residue_evaluation_rank=new_rank,combined_row_rank=joint_rank,
                original_pivot_columns=old_pivots,residue_pivot_columns=new_pivots,
                points=points,residue_rows=rows,
                exact_fraction_dictionary_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),
                linear_forms=len(linear_forms),fraction_records=len(records),
                seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Finite-field evidence only. A rank drop needs an exact zero-residue/nonzero-function witness; equal ranks do not prove uniform or exact rational injectivity.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('points','residue_rows')},indent=2),flush=True)


if __name__=='__main__':main()
