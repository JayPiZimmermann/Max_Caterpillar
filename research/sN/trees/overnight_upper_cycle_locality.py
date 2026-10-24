#!/usr/bin/env python3
"""Exact controls for the Sidon obstruction and circular tie-set count."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math

HERE=Path(__file__).parent


def main():
    tie=(1,2,4,8,16)
    differences=[v-u for u,v in combinations(tie,2)]
    assert len(set(differences))==10 and max(differences)==15
    sidon=[]
    for n in (31,32,37,127):
        assert len({d%n for d in differences}|{-d%n for d in differences})==20
        histogram=Counter();max_edges=0
        for step in range(n):
            if math.gcd(step,n)!=1:continue
            for apex in range(n):
                # This is the cycle in affine order with the apex removed.
                edges={tuple(sorted((i,(i+step)%n))) for i in range(n)
                       if i!=apex and (i+step)%n!=apex}
                edges.add(tuple(sorted(((apex-step)%n,(apex+step)%n))))
                inside=[e for e in edges if set(e)<=set(tie)]
                histogram[len(inside)]+=1;max_edges=max(max_edges,len(inside))
                assert len(inside)<=2
        sidon.append(dict(n=n,affine_cycles=n*sum(math.gcd(i,n)==1 for i in range(n)),
                          induced_edge_histogram=dict(histogram),max_induced_edges=max_edges))
    counts=[]
    for n in range(5,15):
        length=n-1;histogram=Counter()
        for mask in range(1<<length):
            size=mask.bit_count()
            if size in (0,length):continue
            components=sum(bool(mask>>i&1) and not bool(mask>>((i-1)%length)&1) for i in range(length))
            histogram[size,components]+=1
        for m in range(3,n-1):
            inside=histogram[m-1,1]
            outside=histogram[m,1]+histogram[m,2]
            expected=2*length+length*(m-1)*(n-m-2)//2
            assert inside+outside==expected
            counts.append(dict(n=n,m=m,apex_inside=inside,apex_outside=outside,total=expected))
    result=dict(status='EXACT_COMBINATORIAL_CONTROLS_PASS',tie=tie,differences=differences,
                uniform_sidon_claim='For all integers N>=31 the signed differences are distinct modulo N.',
                affine_cycle_controls=sidon,fixed_size_tie_capacity_controls=counts,
                capacity_formula='2*(N-1)+(N-1)*(m-1)*(N-m-2)/2 for 3<=m<=N-2',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Finite arithmetic/count controls; the uniform proofs and CPWL-germ bridge are in the accompanying note, not Lean.')
    (HERE/'overnight_upper_cycle_locality.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',len(sidon),'AFFINE CYCLE CASES',len(counts),'CIRCULAR COUNT CASES')


if __name__=='__main__':main()
