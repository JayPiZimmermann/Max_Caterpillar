#!/usr/bin/env python3
"""Bounded structural audit of actual ordered simplex lifts, not raw powers."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib,json,time
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_single_facet as single
import overnight_upper_ordered_undoubled as undoubled
import overnight_upper_triangle_attachments as attachment
import overnight_upper_ordered_geometric_compress as geometry

HERE=Path(__file__).parent

@lru_cache(None)
def graph(edges):
    return tuple(sorted(tuple(sorted((e.index(max(e)),e.index(min(e))))) for e in edges))

@lru_cache(None)
def pages(g):
    m=len(g);adj=[set() for _ in g]
    for i,j in combinations(range(m),2):
        a,b=g[i];c,d=g[j]
        if a<c<b<d or c<a<d<b:adj[i].add(j);adj[j].add(i)
    order=sorted(range(m),key=lambda i:-len(adj[i]));colors={}
    def color(position,k):
        if position==m:return True
        i=order[position];used={colors[j] for j in adj[i] if j in colors}
        for c in range(k):
            if c in used:continue
            colors[i]=c
            if color(position+1,k):return True
            del colors[i]
        return False
    return next(k for k in range(1,m+1) if color(0,k))

def stats(chain):
    graphs=Counter(graph(edges) for h,edges in chain)
    page_counts=Counter(pages(g) for g in graphs)
    heads={h for h,edges in chain}
    witness=None
    maxpages=max(page_counts)
    for (head,edges),coefficient in chain.items():
        g=graph(edges)
        if pages(g)==maxpages:
            witness=dict(head=head,edges=g,coefficient=coefficient);break
    return dict(terms=len(chain),graphs=len(graphs),heads=len(heads),
                graph_page_counts=sorted(page_counts.items()),
                max_pages=maxpages,max_page_witness=witness,
                max_head_positive_mass=max(sum(max(0,v) for v in h) for h in heads),
                max_positive_nonroot_coordinates=max(sum(v>0 for v in h[1:]) for h in heads),
                max_negative_nonroot_coordinates=max(sum(v<0 for v in h[1:]) for h in heads))

def main():
    start=time.monotonic();records=[]
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X,_=contraction.contract(coherent.delta({k:-v for k,v in triangle.items()},3),4)
    for dimension in (3,4,5,6):
        n=dimension+1;top,pruning=geometry.support_chain(X)
        record=dict(simplex_dimension=dimension,formal_terms=len(X),top=stats(top),pruning=pruning)
        records.append(record)
        print('ACTUAL SUPPORT',json.dumps(record),'SECONDS',time.monotonic()-start,flush=True)
        receipt=dict(status='BOUNDED_ACTUAL_SIMPLEX_SUPPORT_AUDIT',records=records,
                     producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                     seconds=time.monotonic()-start,
                     scope='Exact inventory of the fixed canonical-gauge ordered lifts through dimension6. This does not exclude better gauges or prove an asymptotic count.')
        (HERE/'overnight_upper_actual_support.json').write_text(json.dumps(receipt,indent=2)+'\n')
        if dimension==6:break
        fixed,boundary,_=undoubled.correction(X,n)
        X,_=contraction.contract(single.coface(fixed,n,0),n+1)
        assert coherent.boundary(X)==boundary

if __name__=='__main__':main()
