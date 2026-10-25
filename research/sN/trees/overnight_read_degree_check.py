#!/usr/bin/env python3
"""Integer controls for overlapping-neighborhood Holder and tail bounds."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb,prod
from pathlib import Path
import hashlib,json,time


def main():
    start=time.monotonic();records=[]
    for n in range(1,7):
        possible=list(combinations(range(n),2));tested=0;subsets=0
        for code in range(1<<len(possible)):
            adj=[0]*n
            for j,(u,v) in enumerate(possible):
                if code>>j&1:adj[u]|=1<<v;adj[v]|=1<<u
            degree=[a.bit_count() for a in adj];delta=max(1,max(degree));r=delta+1
            weights=[delta**(n-j) for j in range(n+1)];moment=0
            for selected in range(1<<n):
                z=sum(bool(selected>>v&1) and not(adj[v]&selected) for v in range(n))
                moment+=weights[selected.bit_count()] * 2**(n-z);subsets+=1
            base=r**r
            individual=prod((base-delta**d*r**(r-d-1))*2**r+delta**d*r**(r-d-1) for d in degree)
            common=((base-delta**delta)*2**r+delta**delta)**n
            assert moment**r<=individual<=common
            tested+=1
        records.append(dict(vertices=n,graphs=tested,selected_sets=subsets))
        print(records[-1],flush=True)
    tails=[]
    for delta in range(1,7):
        r=delta+1;p=Q(1,r);q=p*(1-p)**delta
        for blocks in (10,30):
            n=blocks*r;eta=Q(2,n)
            if eta>=q:continue
            nonempty=1-(1-p)**r
            coverage=sum(Q(comb(blocks,j))*nonempty**j*(1-nonempty)**(blocks-j) for j in range(3))
            s=eta*(1-q)/(q*(1-eta))
            assert 0<s<1 and coverage**r*s**2<=(1-q+q*s)**n
            tails.append(dict(vertices=n,maximum_degree=delta,cliques=blocks,
                              exact_coverage=str(coverage),optimized_exponential=str(s)))
    report=dict(status='EXACT_READ_DEGREE_HOLDER_AND_TAIL_CONTROLS_PASS',records=records,tail_controls=tails,
                seconds=time.monotonic()-start,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Finite exact controls of the uniform proof in overnight_read_degree.md.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)


if __name__=='__main__':main()
