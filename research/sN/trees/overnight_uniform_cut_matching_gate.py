#!/usr/bin/env python3
"""Bounded finite-field test of the no-perfect-matching shifted-cut endpoint conjecture.

This is a presentation diagnostic, not a separator proof. All residue
preprocessing is exact. Rank conclusions remain finite-field necessary tests.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib,json,math,random,time
import numpy as np
from overnight_uniform_doublewheel7_single import chart

P=1000003;HERE=Path(__file__).parent


def rank(rows):
    basis={}
    for row in rows:
        v=np.array(row,dtype=np.int64)%P
        for pivot,b in sorted(basis.items()):v=(v-v[pivot]*b)%P
        nz=np.flatnonzero(v)
        if len(nz):
            pivot=int(nz[0]);basis[pivot]=v*pow(int(v[pivot]),P-2,P)%P
    return len(basis)


def main():
    started=time.monotonic();source=HERE/'overnight_lower_matching_rows_7.json';D=json.loads(source.read_text())
    assert D['prime']==P;ids=[];endpoint=[]
    for j,u in enumerate(D['representatives']):
        degree=Counter(v for edge in u['edges']for v in edge)
        hubs=Counter(v for leaf,v in u['edges']if leaf!=u['root']and degree[leaf]==1)
        if True:  # Complete inventory: every nonapex tree has matching number <=2.
            if all(sign==1 or len(C)==1 for C,sign in u['cuts']):endpoint.append(len(ids))
            ids.append(j)
    original=[[r[j]for j in ids]for r in D['modular_rows']]
    original_rank=rank(original);endpoint_rank=rank([[r[j]for j in endpoint]for r in original])
    maps=[]
    for perm in permutations(range(1,7)):
        table=[0]*64
        for mask in range(1,64):
            bit=mask&-mask;j=bit.bit_length()-1
            table[mask]=table[mask^bit]|(1<<perm[j])
        maps.append(table)
    allrows=[];results=[];rng=random.Random(271830)
    for size in range(2,6):
        frequency=chart('minus',size);subsets=[]
        for mask in range(128):subsets.append(tuple(sum(frequency[v][i]for v in range(7)if mask>>v&1)for i in range(6)))
        forms=[];form_ids={};record_ids={};records=[];columns=[]
        def normalize(v):
            g=math.gcd(*v)
            assert g
            if next(x for x in v if x)<0:g=-g
            w=tuple(x//g for x in v)
            if w not in form_ids:form_ids[w]=len(forms);forms.append(w)
            return form_ids[w],g
        edge_cache={}
        for mask in range(1,128):
            if mask&1:continue
            for sign in(-1,1):
                q=subsets[mask];factors=(q,tuple(q[i]+sign*frequency[0][i]for i in range(6)))
                regular=[];scale=1;zero=[]
                for f in factors:
                    if any(f[:5]):j,g=normalize(f[:5]);regular.append(j);scale*=g
                    else:zero.append(f[5])
                edge_cache[mask,sign]=(regular,scale,zero)
        target=sum(1<<v for v in range(1,size+1))
        for j in ids:
            cuts=[(sum(1<<(v-1)for v in C),sign)for C,sign in D['representatives'][j]['cuts']]
            column=Counter()
            for mapping in maps:
                if not any(sign==-1 and mapping[mask]==target for mask,sign in cuts):continue
                regular=[];zero=[];scale=1
                for mask,sign in cuts:
                    r,c,z=edge_cache[mapping[mask],sign];regular+=r;scale*=c;zero+=z
                assert zero==[-1] and len(regular)==9
                key=tuple(sorted(regular))
                if key not in record_ids:record_ids[key]=len(records);records.append(key)
                # (-a)^3 divided by q-a=-s gives +a^3.
                column[record_ids[key]]+=Q(1,scale)
            columns.append([(k,c.numerator*pow(c.denominator,P-2,P)%P)for k,c in column.items()if c])
        assert all(not columns[j]for j in endpoint)
        rows=[];points=[]
        for _ in range(64):
            while True:
                point=tuple(rng.randrange(1,200)for _ in range(5))
                values=[sum(a*b for a,b in zip(f,point))%P for f in forms]
                if all(values):break
            inv=[pow(v,P-2,P)for v in values];top=pow(point[0],3,P);fractions=[]
            for factors in records:
                value=top
                for k in factors:value=value*inv[k]%P
                fractions.append(value)
            rows.append([sum(fractions[k]*c for k,c in col)%P for col in columns]);points.append(point)
        allrows+=rows
        result=dict(subset_size=size,forms=len(forms),records=len(records),rank=rank(rows),cumulative_rank=rank(allrows),points=points,rows=rows)
        results.append(result)
        print('SIZE',size,'rank',result['rank'],'cumulative',result['cumulative_rank'],'seconds',round(time.monotonic()-started,3),flush=True)
    residue_rank=rank(allrows);joint_rank=rank(original+allrows)
    out=dict(status='MODULAR_NO_PERFECT_MATCHING_ENDPOINT_DIAGNOSTIC_ONLY',prime=P,columns=len(ids),endpoint_columns=len(endpoint),
             original_rank=original_rank,endpoint_rank=endpoint_rank,residue_rank=residue_rank,joint_rank=joint_rank,
             dimension_expected_if_endpoint_exact=original_rank-endpoint_rank,
             original_column_indices=ids,endpoint_local_indices=endpoint,results=results,
             seconds=time.monotonic()-started,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='All residue poles considered are nonsingleton shifted-minus cuts, with actual-apex isolation proved in the note. Equal observed dimensions are not an exact rational spanning theorem. A discrepancy requires an independently certified witness.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in('results','original_column_indices','endpoint_local_indices')},indent=2))


if __name__=='__main__':main()
