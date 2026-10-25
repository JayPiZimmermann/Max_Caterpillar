#!/usr/bin/env python3
"""Independent lexicographic-jet controls for the ascending-class flags.

Rebuilds the original nested ReLUs and applies every signed jet directly;
does not import the cut-survival or simplified-germ implementation.
"""
from itertools import combinations,product
from pathlib import Path
import hashlib,json,time

def original_terms(n):
    for choices in product((False,True),repeat=n-2):
        if not any(choices):continue
        spine=[1]+[j+2 for j,c in enumerate(choices) if c]
        edges=[]
        for v in range(2,n):
            previous=[w for w in spine if w<v]
            edges.append((previous[-1],v))
        yield (-1)**(n+sum(choices)),spine[-1],edges

def positive(vector):
    return next((v for v in vector if v),0)>0

def signed_flag_value(n,terms,directions,x):
    total=0
    for signs in product((-1,1),repeat=len(directions)):
        multiplier=1
        for s in signs:multiplier*=s
        points=[tuple(s*d[i] for s,d in zip(signs,directions))+(x[i],) for i in range(n)]
        for coefficient,head,edges in terms:
            vector=[a-b for a,b in zip(points[head],points[0])]
            for u,v in edges:
                edge=tuple(a-b for a,b in zip(points[u],points[v]))
                if positive(edge):vector=[a+b for a,b in zip(vector,edge)]
            if positive(vector):total+=multiplier*coefficient*vector[-1]
    return total

def main():
    started=time.monotonic();records=[]
    for n in range(4,8):
        terms=list(original_terms(n));q=n-1
        for i,j in combinations(range(1,q),2):
            directions=[tuple(int(v==0)-int(v==q) for v in range(n))]
            directions.extend(tuple(-int(v==r) for v in range(n))
                for r in range(1,q) if r not in (i,j))
            x=tuple(int(v==0) for v in range(n));y=tuple(int(v==i) for v in range(n))
            z=tuple(a+b for a,b in zip(x,y));minus=lambda p:tuple(-a for a in p)
            points=[z,minus(z),x,minus(x),y,minus(y)]
            values=[signed_flag_value(n,terms,directions,p) for p in points]
            defect=sum(w*v for w,v in zip((1,-1,-1,1,-1,1),values))
            assert defect==1,(n,i,j,values)
            assert len(directions)==n-3
            survivors=[(a,b) for a,b in combinations(range(n),2)
                if all(d[a]==d[b] for d in directions)]
            assert survivors==[(i,j)]
            records.append(dict(labels=n,retained_pair=[i,j],jet_values=values,defect=defect))
    receipt=dict(status='INDEPENDENT_EXACT_ASCENDING_CLASS_JET_FLAGS_PASS',
        records=records,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=time.monotonic()-started,
        scope='Independent controls of the uniform written cut-survival proof; excludes one sparse graph per class, not the global family or maximum.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status'],'CASES',len(records),'SECONDS',receipt['seconds'])

if __name__=='__main__':main()
