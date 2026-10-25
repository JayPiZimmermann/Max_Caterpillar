#!/usr/bin/env python3
"""Exact finite controls of the uniform connected-set counting proof."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib,json,time


def components(adj,mask):
    count=0
    while mask:
        count+=1;front=mask&-mask;mask^=front
        while front:
            bit=front&-front;front^=bit
            fresh=adj[bit.bit_length()-1]&mask;mask^=fresh;front|=fresh
    return count


def main():
    start=time.monotonic();records=[]
    for n in range(1,7):
        possible=list(combinations(range(n),2));tested=subsets=0
        for code in range(1<<len(possible)):
            adj=[0]*n
            for j,(u,v) in enumerate(possible):
                if code>>j&1:adj[u]|=1<<v;adj[v]|=1<<u
            delta=max(3,max(a.bit_count() for a in adj));b=Q(1,delta-2);critical=b/(1+b)**(delta-1);C=b*(1+b)
            connected=[0]*(n+1);low=[0]*(n+1);rooted=[[0]*(n+1) for _ in range(n)]
            for selected in range(1<<n):
                count=components(adj,selected);size=selected.bit_count();subsets+=1
                if count<=2:low[size]+=1
                if count==1:
                    connected[size]+=1
                    for v in range(n):rooted[v][size]+=int(bool(selected>>v&1))
            for m in range(1,n+1):
                numerator=comb((delta-1)*m,m-1)+(2*comb((delta-1)*m,m-2) if m>=2 else 0)
                assert numerator%m==0
                rm=numerator//m
                assert all(row[m]<=rm for row in rooted)
                assert m*connected[m]<=n*rm
                assert 2*(low[m]-connected[m])<=sum(connected[j]*connected[m-j] for j in range(1,m))
            for y in set((critical,min(critical,Q(1,6)))):
                a,d=y.numerator,y.denominator;den=d**n;weights=[a**j*d**(n-j) for j in range(n+1)]
                A=sum(c*w for c,w in zip(connected,weights));L=sum(c*w for c,w in zip(low,weights))
                assert A*C.denominator<=n*C.numerator*den
                for row in rooted:assert sum(c*w for c,w in zip(row,weights))*C.denominator<=C.numerator*den
                assert 2*L*den<=2*den*den+2*A*den+A*A
                assert 2*L*C.denominator**2<=den*(2*C.denominator**2+2*n*C.numerator*C.denominator+n*n*C.numerator**2)
            tested+=1
        records.append(dict(vertices=n,graphs=tested,selected_sets=subsets));print(records[-1],flush=True)
    report=dict(status='EXACT_CONNECTED_DEGREE_CONTROLS_PASS',records=records,seconds=time.monotonic()-start,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite controls of the uniform proof in overnight_connected_degree.md.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)


if __name__=='__main__':main()
