#!/usr/bin/env python3
"""Exhaustive exact controls for the uniform bounded-excess witness proof."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib,json,time


def component_count(adj, mask):
    count=0
    while mask:
        count+=1; frontier=mask & -mask; mask^=frontier
        while frontier:
            bit=frontier & -frontier;frontier^=bit
            fresh=adj[bit.bit_length()-1]&mask
            mask^=fresh;frontier|=fresh
    return count


def main():
    start=time.monotonic();records=[]
    for n in range(1,7):
        possible=list(combinations(range(n),2)); tested=nonpseudo=subsets=0
        for code in range(1<<len(possible)):
            edges=[e for j,e in enumerate(possible) if code>>j&1]
            adj=[0]*n
            for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
            @lru_cache(None)
            def match(mask):
                if not mask:return ()
                bit=mask&-mask;v=bit.bit_length()-1;rest=mask^bit
                best=match(rest); options=adj[v]&rest
                while options:
                    other=options&-options;options^=other;w=other.bit_length()-1
                    candidate=((v,w),)+match(rest^other)
                    if len(candidate)>len(best):best=candidate
                return best
            matching=match((1<<n)-1)
            groups=list(range(n))
            def find(v):
                while groups[v]!=v:v=groups[v]
                return v
            kept=[]
            for u,v in list(matching)+edges:
                a,b=find(u),find(v)
                if a!=b:groups[a]=b;kept.append(tuple(sorted((u,v))))
            keep=set(kept);cyclic=set()
            for edge in edges:
                if edge not in keep and find(edge[0]) not in cyclic:
                    keep.add(edge);cyclic.add(find(edge[0]))
            vertex_counts=Counter(find(v) for v in range(n));edge_counts=Counter(find(u) for u,v in edges)
            excess=sum(max(0,edge_counts[c]-size) for c,size in vertex_counts.items())
            assert len(edges)-len(keep)==excess
            assert all(tuple(sorted(e)) in keep for e in matching)
            padj=[0]*n;core=[set() for _ in range(n)]
            for u,v in keep:padj[u]|=1<<v;padj[v]|=1<<u;core[u].add(v);core[v].add(u)
            assert [not a for a in adj]==[not a for a in padj]
            remaining=set(range(n));parent={}
            while True:
                leaf=next((v for v in sorted(remaining) if len(core[v])<=1),None)
                if leaf is None:break
                parent[leaf]=next(iter(core[leaf]),None)
                if parent[leaf] is not None:core[parent[leaf]].remove(leaf)
                remaining.remove(leaf)
            while remaining:
                first=min(remaining);previous=None;v=first
                while True:
                    w=next(w for w in sorted(core[v]) if w!=previous)
                    parent[w]=v;remaining.remove(v)
                    if w==first:break
                    previous,v=v,w
            assert len(parent)==n
            assert all(parent[u]==v or parent[v]==u for u,v in keep)
            children=[v if parent[v]==u else u for u,v in matching]
            isolated=[v for v in range(n) if not adj[v]]
            k=len(matching)+len(isolated);low=0
            for selected in range(1<<n):
                witnesses=sum(bool(selected>>v&1) and not(selected>>parent[v]&1) for v in children)
                witnesses+=sum(bool(selected>>v&1) for v in isolated)
                pc=component_count(padj,selected);gc=component_count(adj,selected)
                assert witnesses<=pc and gc>=pc-excess
                if gc<=2:
                    assert witnesses<=excess+2;low+=1
                subsets+=1
            tail=sum(comb(k,j)*3**(k-j) for j in range(min(k,excess+2)+1))
            assert low*4**k<=tail*2**n
            tested+=1;nonpseudo+=bool(excess)
        records.append(dict(vertices=n,graphs=tested,nonpseudoforests=nonpseudo,selected_sets=subsets))
        print(records[-1],flush=True)
    result=dict(status='EXACT_BOUNDED_EXCESS_CONTROLS_PASS',records=records,seconds=time.monotonic()-start,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite controls of the uniform mathematical proof.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)


if __name__=='__main__':main()
