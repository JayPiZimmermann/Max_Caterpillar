#!/usr/bin/env python3
"""Shorten a proposed rational null basis using recorded invertible row moves.

This is only a proof-search operation. Every resulting vector still needs an
exact rational-function gate, and replay of the row-operation log certifies
independence from the original free-column identity submatrix.
"""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import statistics
import sys
import time

import overnight_upper_probe as P

HERE=Path(__file__).parent


def main(mode,limit,steps):
    started=time.monotonic();source=P.stem(mode).with_suffix('.json');original=json.loads(source.read_text())
    dest=HERE/f'overnight_upper_{mode}_sparse_kernels.json'
    if dest.exists():
        saved=json.loads(dest.read_text());assert saved['source_sha256']==P.digest(source)
        rows=[{j:Q(c) for j,c in row} for row in saved['vectors']];moves=saved['moves']
    else:
        rows=[{j:Q(c) for j,c in row} for row in original['kernel_proposals']];moves=[]
        free=set(original['kernel_free_columns'])
        for f,row in zip(original['kernel_free_columns'],rows):assert {j:c for j,c in row.items() if j in free}=={f:Q(1)}
    before=[len(row) for row in rows];pool=[i for i,row in enumerate(rows) if len(row)<=32]
    inverted=defaultdict(list)
    for i in pool:
        for j in rows[i]:inverted[j].append(i)
    targets=sorted((i for i,row in enumerate(rows) if len(row)>32),key=lambda i:-len(rows[i]))[:limit]
    print('LOAD','TOTAL',sum(before),'MAX',max(before),'POOL',len(pool),'TARGETS',len(targets),
          'SECONDS',time.monotonic()-started,flush=True)
    for number,i in enumerate(targets):
        v=rows[i];initial=len(v);count=0
        for unused in range(steps):
            overlaps=Counter(k for j in v for k in inverted.get(j,()))
            candidates=[(2*m-len(rows[k]),k,m) for k,m in overlaps.items() if 2*m>len(rows[k])]
            candidates.sort(reverse=True);best=None
            for possible,k,m in candidates[:96]:
                u=rows[k];missing=len(u)-m
                ratios=Counter(v[j]/c for j,c in u.items() if j in v)
                c,cancels=ratios.most_common(1)[0];gain=cancels-missing
                if gain>0 and (best is None or gain>best[0]):best=(gain,k,c)
                if best is not None and best[0]>=possible:break
            if best is None:break
            gain,k,c=best
            oldlen=len(v)
            for j,a in rows[k].items():
                value=v.get(j,Q(0))-c*a
                if value:v[j]=value
                else:v.pop(j,None)
            assert v and len(v)==oldlen-gain
            moves.append([i,k,str(c)]);count+=1
            if len(v)<=32:break
        print('REDUCE',i,initial,'TO',len(v),'MOVES',count,'SECONDS',time.monotonic()-started,flush=True)
        if time.monotonic()-started>1000:break
    after=[len(row) for row in rows]
    data=dict(status='SPARSE_BASIS_PROPOSAL_PENDING_EXACT_GATES',mode=mode,source=source.name,
              source_sha256=P.digest(source),producer_sha256=P.digest(Path(__file__)),
              original_free_columns=original['kernel_free_columns'],vectors=[[[j,str(c)] for j,c in sorted(row.items())] for row in rows],
              moves=moves,total_support=sum(after),max_support=max(after),median_support=statistics.median(after),
              elapsed_seconds_this_run=time.monotonic()-started)
    dest.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE TOTAL',sum(before),'TO',sum(after),'MAX',max(before),'TO',max(after),'MOVES',len(moves),flush=True)


if __name__=='__main__':main(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 20,int(sys.argv[3]) if len(sys.argv)>3 else 50)
