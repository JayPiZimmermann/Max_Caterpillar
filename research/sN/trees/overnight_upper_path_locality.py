#!/usr/bin/env python3
"""Complete noncrossing-path inventories and alternating-tie rank controls."""
from itertools import product,permutations
from pathlib import Path
import hashlib,json,time

HERE=Path(__file__).parent


def normalize(edges):return tuple(sorted(tuple(sorted(e)) for e in edges))


def crosses(e,f):
    a,b=sorted(e);c,d=sorted(f)
    return a<c<b<d or c<a<d<b


def paths(n):
    out=set()
    for first in range(n):
        for mask in range(1<<max(0,n-2)):
            left,right=1,n-1;order=[first]
            for j in range(n-2):
                if mask>>j&1:order.append((first+right)%n);right-=1
                else:order.append((first+left)%n);left+=1
            order.append((first+left)%n)
            edges=normalize(zip(order,order[1:]));assert not any(crosses(e,f) for e in edges for f in edges)
            out.add(edges)
    assert len(out)==n*(1<<(n-3))
    return sorted(out)


def main():
    started=time.monotonic();controls=[]
    for n in range(3,8):
        brute={normalize(zip(p,p[1:])) for p in permutations(range(n))
               if not any(crosses(e,f) for e in zip(p,p[1:]) for f in zip(p,p[1:]))}
        got=set(paths(n));assert got==brute;controls.append(dict(n=n,count=len(got)))
    results=[]
    for n in range(7,15):
        tie=set(range(0,n,2));family=paths(n-1);best=-1;witness=None
        for apex in range(n):
            vertices=[v for v in range(n) if v!=apex]
            for edges in family:
                count=sum(vertices[u] in tie and vertices[v] in tie for u,v in edges)
                if count>best:best=count;witness=dict(apex=apex,edges=[(vertices[u],vertices[v]) for u,v in edges])
        results.append(dict(n=n,tie=sorted(tie),path_graphs=n*len(family),max_free_rank=best,
                            necessary_free_rank=len(tie)-2,obstruction=best<len(tie)-2,witness=witness))
        print(results[-1],flush=True)
    out=dict(status='COMPLETE_NONCROSSING_PATH_TIE_RANK_CONTROLS',controls=controls,results=results,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
    (HERE/'overnight_upper_path_locality.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
