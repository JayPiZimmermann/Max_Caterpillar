#!/usr/bin/env python3
"""Compact independently regenerated evaluation minor for the cycle exclusion."""
from pathlib import Path
import hashlib,json,math,time
import numpy as np

import overnight_upper_weighted_paths as W

HERE=Path(__file__).parent
CYCLES=HERE.parent/'cycles'
BASE=CYCLES/'overnight_cycle_symmetric_7'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def rank(rows,prime):
    work=[row.copy() for row in rows];rank=0
    for col in range(len(work[0])):
        pivot=next((i for i in range(rank,len(work)) if work[i][col]%prime),None)
        if pivot is None:continue
        work[rank],work[pivot]=work[pivot],work[rank];pivotrow=work[rank];inverse=pow(pivotrow[col],-1,prime)
        for i in range(rank+1,len(work)):
            factor=work[i][col]*inverse%prime
            if factor:
                for j in range(col,len(pivotrow)):work[i][j]=(work[i][j]-factor*pivotrow[j])%prime
        rank+=1
        if rank==len(work):break
    return rank


def main():
    started=time.monotonic();inventory=json.loads(BASE.with_suffix('.inventory.json').read_text())
    prepare=json.loads(BASE.with_suffix('.prepare.json').read_text());gate=json.loads(BASE.with_suffix('.exact.json').read_text())
    selected=gate['independent_augmented_rows'];assert len(selected)==127
    signatures=W.family(7,'unit1');lookup={s:i for i,s in enumerate(signatures)};dag=W.Compiler(7).compile(signatures)
    mapping=[];seen=set()
    for original,((head,edges),atoms) in enumerate(inventory['representatives']):
        if len(edges)!=5:continue
        assert edges==[[i,i+1] for i in range(1,6)] and head[0]==-1 and sum(head)==0
        signature=tuple((sum(head[i:])-1,1) for i in range(2,7));canonical=W.canonical(signature)
        automorphisms=2 if signature==tuple((1-h-w,w) for h,w in signature[::-1]) else 1
        assert canonical not in seen;seen.add(canonical)
        mapping.append(dict(original_column=original,dp_column=lookup[canonical],signature=canonical,automorphisms=automorphisms))
    assert seen==set(signatures) and len(mapping)==138
    source=np.fromfile(BASE.with_suffix('.u32'),dtype=np.uint32).reshape(-1,len(inventory['representatives'])+1)
    points=[prepare['points'][i] for i in selected];rows=[]
    for row_index,point in zip(selected,points):
        values=dag.evaluate(point,W.P)
        row=[values[item['dp_column']]*pow(item['automorphisms'],-1,W.P)%W.P for item in mapping]
        row.append(pow(math.prod(point)%W.P,-1,W.P))
        assert row==list(map(int,source[row_index,[item['original_column'] for item in mapping]+[len(inventory['representatives'])]]))
        rows.append(row)
    ranks=[rank([row[:-1] for row in rows],W.P),rank(rows,W.P)];assert ranks==[126,127]
    out=dict(status='COMPLETE_INDEPENDENT_DP_MINOR_REPLAY_PASS',n=7,prime=W.P,points=points,modular_rows=rows,
             column_mapping=mapping,selected_original_rows=selected,ranks=ranks,
             inventory_sha256=sha(BASE.with_suffix('.inventory.json')),prepare_sha256=sha(BASE.with_suffix('.prepare.json')),
             original_matrix_sha256=sha(BASE.with_suffix('.u32')),dp_producer_sha256=sha(Path(W.__file__)),
             producer_sha256=sha(Path(__file__)),seconds=time.monotonic()-started,
             exact_scope='This minor proves augmented characteristic-zero rank at least127; ordinary rank at most126 requires the separate twelve exact rational-function kernel identities.')
    (HERE/'overnight_upper_cycle_minor_7.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS',len(rows),'ROWS',len(mapping),'COLUMNS','RANKS',ranks,'SECONDS',out['seconds'],flush=True)


if __name__=='__main__':main()
