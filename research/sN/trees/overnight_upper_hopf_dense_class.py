#!/usr/bin/env python3
"""Uniform ascending-class flag formula, checked at complete small arities."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import hashlib,json
from overnight_upper_hopf_locality import prune_D,value
HERE=Path(__file__).parent

def ascending_target(n):
    output=defaultdict(int)
    for mask in range(1,1<<(n-2)):
        spine=[1]+[v for v in range(2,n) if mask>>(v-2)&1]
        head=[-1]+[0]*(n-1);head[max(spine)]=1
        edges=tuple((max(v for v in spine if v<j),j) for j in range(2,n))
        output[(tuple(head),edges)]+=(-1)**(n+mask.bit_count())
    return dict(output)

def odd(chain,x,y):
    neg=lambda v:tuple(-a for a in v);z=tuple(a+b for a,b in zip(x,y))
    return value(chain,z)-value(chain,neg(z))-value(chain,x)+value(chain,neg(x))-value(chain,y)+value(chain,neg(y))

def main():
    records=[]
    for n in range(4,11):
        q=n-1;target=ascending_target(n);u=tuple(int(k==0)-int(k==q) for k in range(n))
        first=prune_D(target,u);checks=0
        for i,j in combinations(range(1,q),2):
            current=first
            deleted=[v for v in range(1,q) if v not in (i,j)]
            for v in deleted:current=prune_D(current,tuple(-int(k==v) for k in range(n)))
            top={key:c for key,c in current.items() if key[1]}
            expected={}
            for r,c in ((i,int(i>=2)),(j,-1)):
                h=tuple(2*int(k==r)-int(k==0)-int(k==q) for k in range(n))
                if c:expected[(h,((i,j),))]=c
            assert top==expected,(n,i,j,top,expected)
            x=(1,)+(0,)*(n-1);y=tuple(int(k==i) for k in range(n))
            assert odd(current,x,y)==1
            directions=[u]+[tuple(-int(k==v) for k in range(n)) for v in deleted]
            for a,b in combinations(range(n),2):
                assert all(d[a]==d[b] for d in directions)==((a,b)==(i,j))
            checks+=1
        records.append(dict(labels=n,pairs_checked=checks,required_comparison_edges=(n-2)*(n-3)//2))
    result=dict(status='EXACT_UNIFORM_ASCENDING_CLASS_FLAG_CONTROLS_PASSED',records=records,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Complete finite convention checks throughN10 for the adjacent uniform cut-survival proof. Requires a quadratic total comparison graph for this individual class, not for the full maximum.')
    (HERE/'overnight_upper_hopf_dense_class.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'TOTAL_PAIRS',sum(r['pairs_checked'] for r in records))

if __name__=='__main__':main()
