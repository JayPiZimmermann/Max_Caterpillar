#!/usr/bin/env python3
"""Exact gates cached by vector content, plus row-operation independence replay."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys
import time

import overnight_upper_probe as P
from rational_identity import Verifier,add

HERE=Path(__file__).parent


def normalized(raw):return [[j,str(Q(c))] for j,c in sorted(raw)]
def key(raw):return hashlib.sha256(json.dumps(normalized(raw),separators=(',',':')).encode()).hexdigest()


def main(mode,limit,cutoff):
    started=time.monotonic();source=P.stem(mode).with_suffix('.json')
    sparse=HERE/f'overnight_upper_{mode}_sparse_kernels.json';cache_path=HERE/f'overnight_upper_{mode}_kernel_cache.json'
    data=json.loads(sparse.read_text());assert data['source_sha256']==P.digest(source)
    orbits,sources=P.source_orbits(mode)
    cache=json.loads(cache_path.read_text()) if cache_path.exists() else dict(status='PARTIAL_EXACT_KERNEL_CACHE',sources=sources,verified=[])
    assert cache['sources']==sources
    known={entry['sha256'] for entry in cache['verified']}
    candidates=sorted((normalized(v) for v in data['vectors'] if len(v)<=cutoff),key=len)
    forms=[tuple(int(i==j) for i in range(6))+(0,) for j in range(6)]+[(-1,)*6+(0,)]
    one=(0,)*6+(1,);done=0;V=Verifier(budget=1050)
    for raw in candidates:
        sha=key(raw)
        if sha in known:continue
        expr=P.exact_expression(7,[orbits[j] for j,c in raw],[Q(c) for j,c in raw]);add(expr,1,one,0,[(f,1) for f in forms])
        try:ok=V.check(expr)
        except TimeoutError:break
        assert ok
        entry=dict(sha256=sha,vector=raw,kind='EXACT_PRINCIPAL_PARTS')
        cache['verified'].append(entry);known.add(sha);done+=1
        if done%25==0:
            cache.update(checker_sha256=P.digest(Path(__file__)),last_run_seconds=time.monotonic()-started)
            cache_path.write_text(json.dumps(cache,separators=(',',':'))+'\n')
            print('EXACT',done,'CACHED',len(known),'SECONDS',time.monotonic()-started,flush=True)
        if done>=limit or time.monotonic()-started>1000:break
    cache.update(checker_sha256=P.digest(Path(__file__)),last_run_seconds=time.monotonic()-started)
    cache_path.write_text(json.dumps(cache,separators=(',',':'))+'\n')
    print('DONE VERIFIED',done,'TOTAL CACHE',len(known),flush=True)


def replay(mode):
    source=P.stem(mode).with_suffix('.json');original=json.loads(source.read_text())
    sparse=HERE/f'overnight_upper_{mode}_sparse_kernels.json';data=json.loads(sparse.read_text())
    assert data['source_sha256']==P.digest(source)
    rows=[{j:Q(c) for j,c in row} for row in original['kernel_proposals']]
    free=set(original['kernel_free_columns'])
    for f,row in zip(original['kernel_free_columns'],rows):assert {j:c for j,c in row.items() if j in free}=={f:Q(1)}
    for i,k,coefficient in data['moves']:
        assert i!=k;c=Q(coefficient)
        for j,a in rows[k].items():
            value=rows[i].get(j,Q(0))-c*a
            if value:rows[i][j]=value
            else:rows[i].pop(j,None)
    assert [normalized(list(row.items())) for row in rows]==data['vectors']
    cache_path=HERE/f'overnight_upper_{mode}_kernel_cache.json';cache=json.loads(cache_path.read_text())
    known={entry['sha256'] for entry in cache['verified']}
    covered=sum(key(raw) in known for raw in data['vectors'])
    result=dict(status='INDEPENDENCE_REPLAY_PASS_PARTIAL_EXACT_GATES',source_sha256=P.digest(source),
                sparse_sha256=P.digest(sparse),cache_sha256=P.digest(cache_path),checker_sha256=P.digest(Path(__file__)),
                independent_vectors=len(rows),invertible_row_moves=len(data['moves']),exact_vectors_covered=covered,
                augmented_modular_rank=original['ranks'][1],ordinary_rank_upper_pending=original['orbit_columns']-len(rows))
    if covered==len(rows):
        assert result['ordinary_rank_upper_pending']<result['augmented_modular_rank']
        result['status']='EXACT_FULL_BALANCED_TOP_OBSTRUCTION' if mode=='balanced' else 'EXACT_TOP_OBSTRUCTION'
    (HERE/f'overnight_upper_{mode}_sparse_gate.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)


if __name__=='__main__':
    if sys.argv[2]=='replay':replay(sys.argv[1])
    else:main(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 32)
