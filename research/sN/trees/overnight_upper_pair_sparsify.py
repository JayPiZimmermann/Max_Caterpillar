#!/usr/bin/env python3
"""Find short differences between dense null vectors by exact MinHash proposals."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import heapq
import json
import statistics
import sys
import time

import overnight_upper_probe as P

HERE=Path(__file__).parent


def scale(row):
    counts=Counter(abs(c) for c in row.values());s=max(counts,key=lambda x:(counts[x],-x))
    return s if row[min(row)]>0 else -s


def main(mode,rounds,limit):
    started=time.monotonic();path=HERE/f'overnight_upper_{mode}_sparse_kernels.json';data=json.loads(path.read_text())
    assert data['source_sha256']==P.digest(P.stem(mode).with_suffix('.json'))
    rows=[{j:Q(c) for j,c in row} for row in data['vectors']];moves=data['moves'];before=sum(map(len,rows))
    print('LOADED',len(rows),'TOTAL',before,'SECONDS',time.monotonic()-started,flush=True)
    scales=[scale(row) for row in rows]
    for round_no in range(rounds):
        buckets=defaultdict(list)
        for i,row in enumerate(rows):
            if len(row)<=32:continue
            s=scales[i]
            def features():
                for j,c in row.items():
                    q=c/s
                    yield hash((j,q.numerator,q.denominator))&((1<<64)-1)
            smallest=heapq.nsmallest(6,features())
            for band in range(3):buckets[band,tuple(smallest[2*band:2*band+2])].append(i)
        pairs=Counter()
        for bucket in buckets.values():
            bucket.sort(key=lambda i:len(rows[i]))
            if len(bucket)<=16:
                for i,j in combinations(bucket,2):pairs[tuple(sorted((i,j)))]+=1
            else:
                for pos,i in enumerate(bucket):
                    for j in bucket[pos+1:pos+9]:pairs[tuple(sorted((i,j)))]+=1
        print('ROUND',round_no,'CANDIDATES',len(pairs),'SECONDS',time.monotonic()-started,flush=True)
        done=0;gain_total=0
        for (i,j),votes in pairs.most_common(limit):
            if len(rows[i])<len(rows[j]):i,j=j,i
            v,u=rows[i],rows[j]
            if len(v)<=32:continue
            c=scales[i]/scales[j];overlap=plus=minus=0
            for p,a in u.items():
                if p in v:
                    overlap+=1
                    if v[p]==c*a:plus+=1
                    if v[p]==-c*a:minus+=1
            if minus>plus:c=-c;plus=minus
            gain=plus-(len(u)-overlap)
            if gain<max(3,len(v)//50):continue
            oldlen=len(v)
            for p,a in u.items():
                q=v.get(p,Q(0))-c*a
                if q:v[p]=q
                else:v.pop(p,None)
            assert v and len(v)==oldlen-gain
            scales[i]=scale(v);moves.append([i,j,str(c)]);done+=1;gain_total+=gain
            if done%25==0:print('PAIRS',done,'SAVED',gain_total,'SECONDS',time.monotonic()-started,flush=True)
            if time.monotonic()-started>950:break
        print('ROUND DONE',done,'SAVED',gain_total,flush=True)
        if time.monotonic()-started>950 or not done:break
    lengths=list(map(len,rows));data.update(vectors=[[[j,str(c)] for j,c in sorted(row.items())] for row in rows],moves=moves,
        total_support=sum(lengths),max_support=max(lengths),median_support=statistics.median(lengths),
        producer_sha256=P.digest(Path(__file__)),elapsed_seconds_this_run=time.monotonic()-started)
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE SUPPORT',before,'TO',sum(lengths),'MAX',max(lengths),'MOVES',len(moves),flush=True)


if __name__=='__main__':main(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 2,int(sys.argv[3]) if len(sys.argv)>3 else 10000)
