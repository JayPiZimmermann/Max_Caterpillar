#!/usr/bin/env python3
"""Exact all-real locality obstruction for the smallest Baxter union graph.

Rebuilds the word target without hinge normalization or Fourier evaluation.
"""
from collections import defaultdict
from pathlib import Path
import hashlib,json

HERE=Path(__file__).parent

def bst(word):
    if not word:return ()
    r=word[0];left=tuple(v for v in word[1:] if v<r);right=tuple(v for v in word[1:] if v>r)
    return tuple(sorted(bst(left)+bst(right)+(((r,left[0]),) if left else ())+
                        (((r,right[0]),) if right else ())))

def words_target(words):
    n=5;out=defaultdict(int)
    for word in words:
        for bits in range(1,8):
            spine=[0]+[i for i in range(1,4) if bits>>(i-1)&1]
            h=[-1,0,0,0,0];h[word[max(spine)]]=1
            edges=tuple(sorted((word[max(k for k in spine if k<j)],word[j]) for j in range(1,4)))
            out[(tuple(h),edges)]+=(-1)**(n+bits.bit_count())
    return {u:c for u,c in out.items() if c}

def delete_mod_shallow(chain,v):
    out=defaultdict(int)
    for (h,edges),c in chain.items():
        for direction in (-1,1):
            head=list(h);free=[];outer=direction*h[v]
            for i,j in edges:
                slope=direction*(int(i==v)-int(j==v))
                outer+=max(0,slope)
                if not slope:free.append((i,j))
                elif slope>0:head[i]+=1;head[j]-=1
            if outer==0:
                assert head[v]==0
                out[(tuple(head),tuple(free))]+=-direction*c
    return {u:c for u,c in out.items() if c}

def value(chain,x):
    return sum(c*max(0,sum(a*b for a,b in zip(h,x))+
                        sum(max(0,x[i]-x[j]) for i,j in edges))
               for (h,edges),c in chain.items())

def main():
    words=((3,1,4,2),(3,4,1,2))
    pairs=[(bst(w),bst(w[::-1])) for w in words]
    assert pairs[0]==pairs[1]
    graph=sorted({tuple(sorted(e)) for tree in pairs[0] for e in tree})
    remaining={0,1,4}
    assert not [e for e in graph if set(e)<=remaining]
    original=words_target(words);records=[]
    for order in ((2,3),(3,2)):
        reduced=original
        for v in order:reduced=delete_mod_shallow(reduced,v)
        x=(0,1,0,0,0);y=(0,0,0,0,1);xy=tuple(a+b for a,b in zip(x,y))
        odd=lambda v:value(reduced,v)-value(reduced,tuple(-a for a in v))
        values=[odd(x),odd(y),odd(xy)]
        score=values[2]-values[0]-values[1]
        assert score==-4
        records.append(dict(deletion_order=order,reduced_units=[[h,edges,c] for (h,edges),c in sorted(reduced.items())],
                            odd_values=values,additivity_defect=score))
    result=dict(status='EXACT_ALL_REAL_BAXTER_UNION_GRAPH_LOCALITY_OBSTRUCTION',
                words=words,twin_pair=pairs[0],union_graph=graph,
                remaining_labels=sorted(remaining),induced_edges=[],
                raw_word_target_terms=len(original),records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Any number of second-hidden-layer units with comparison graph contained in this fixed omitted-apex union graph, arbitrary real inner/output coefficients and heads, plus a shallow or L3 remainder. It excludes the classwise bridge, not all Baxter-derived constructions.')
    (HERE/'overnight_upper_baxter_locality.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'DEFECTS',[r['additivity_defect'] for r in records],flush=True)

if __name__=='__main__':main()
