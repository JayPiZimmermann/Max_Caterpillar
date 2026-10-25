"""Exact conversion of an anchored pair network into the full comparison span."""
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path


def convert_network(path,reference=4):
    net=json.loads(Path(path).read_text());N=net['N'];assert reference==N-1;pairs=list(combinations(range(N),2));physical=[list(map(Q,r))for r in net['first_layer']];weights=[list(map(Q,r))for r in net['second_layer']];outputs=list(map(Q,net['output']));assert outputs[:2]==[1,-1]and weights[1]==[-v for v in weights[0]]
    def convert(w,head=False):
        out=[Q(0)]*len(pairs);linear=[Q(0)]*N;carriers={}
        for row,c in zip(physical,w):
            nz=[i for i,v in enumerate(row)if v]
            if len(nz)==1:carriers[nz[0],int(row[nz[0]])]=c;continue
            i=next(i for i,v in enumerate(row)if v>0);j=next(i for i,v in enumerate(row)if v<0);assert row[i]==1 and row[j]==-1;out[pairs.index(tuple(sorted((i,j))))]+=c
            if i>j:linear[i]+=c;linear[j]-=c
        for i in{j for j,sgn in carriers}:assert carriers[i,1]==-carriers[i,-1];linear[i]+=carriers[i,1]
        if head:linear[reference]-=1
        assert sum(linear)==0
        return out+linear[:-1]
    core=[(1 if d>0 else-1,[abs(d)*v for v in convert(w)])for d,w in zip(outputs[2:],weights[2:])];core.sort(key=lambda z:-z[0]);return pairs,convert(weights[0],True),core
