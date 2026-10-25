#!/usr/bin/env python3
"""Explicit sparse contraction of the normalized exterior graph complex.

Half-edge partition formulas are checked before passing to the graph quotient.
No asymptotic network-width claim is made.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib,json,random,time
import overnight_upper_ordered_normalized as normalized

HERE=Path(__file__).parent


def clean(d):return {k:v for k,v in d.items() if v}


def linear_add(out,terms,scale=1):
    for key,value in terms.items():out[key]+=scale*value


def rename(partition,a,b):
    return tuple(tuple(sorted(b if x==a else a if x==b else x for x in block)) for block in partition)


def partition_delta(partition):
    out=defaultdict(int)
    for i,block in enumerate(partition):
        for mask in range(1,(1<<len(block))-1):
            left=tuple(v for j,v in enumerate(block) if mask>>j&1)
            right=tuple(v for j,v in enumerate(block) if not mask>>j&1)
            out[partition[:i]+(left,right)+partition[i+1:]]+=(-1)**(i+1)
    return clean(out)


def P(partition,a):
    for i,block in enumerate(partition):
        if a in block:
            if len(block)>1:return {}
            return {partition[:i]+partition[i+1:]+((a,),):(-1)**(len(partition)-i-1)}
    raise AssertionError('missing distinguished half-edge')


def H(partition,a):
    out=defaultdict(int)
    for i,block in enumerate(partition):
        if a not in block:continue
        if len(block)>1:return {}
        for j in range(i+1,len(partition)):
            blocks=list(partition[:i]+partition[i+1:])
            blocks[j-1]=tuple(sorted(blocks[j-1]+(a,)))
            out[tuple(blocks)]+=(-1)**(i+1)
        return clean(out)
    raise AssertionError('missing distinguished half-edge')


def H_two_projection(partition,a,b):
    out=defaultdict(int)
    linear_add(out,H(partition,a))
    for projected,coefficient in P(partition,a).items():linear_add(out,H(projected,b),coefficient)
    return clean(out)


def H_transposition(partition,a,b):
    out=defaultdict(int)
    linear_add(out,H_two_projection(partition,a,b))
    linear_add(out,H_two_projection(rename(partition,a,b),a,b))
    return clean(out)


def H_edge_exchange(partition,a,b,c,d):
    out=defaultdict(int)
    linear_add(out,H_transposition(partition,a,c))
    for key,value in H_transposition(partition,b,d).items():out[rename(key,a,c)]-=value
    return clean(out)


def compose_boundary_identity(partition,homotopy):
    out=defaultdict(int)
    for key,value in homotopy(partition).items():linear_add(out,partition_delta(key),value)
    for key,value in partition_delta(partition).items():linear_add(out,homotopy(key),value)
    return clean(out)


def ordered_partitions(n):
    result=[()]
    for a in range(n):
        new=[]
        for partition in result:
            for i in range(len(partition)):
                new.append(partition[:i]+(partition[i]+(a,),)+partition[i+1:])
            for i in range(len(partition)+1):new.append(partition[:i]+((a,),)+partition[i:])
        result=new
    return result


def graph_partition(q,graph):
    blocks=[[] for _ in range(q)]
    for i,(u,v) in enumerate(graph):blocks[u].append(2*i);blocks[v].append(2*i+1)
    assert all(blocks)
    return tuple(tuple(b) for b in blocks)


def project_graph(partition,k):
    position={a:i for i,block in enumerate(partition) for a in block}
    edges=[];sign=1
    for i in range(k):
        u,v=position[2*i],position[2*i+1]
        if u==v:return None
        if u>v:u,v=v,u;sign=-sign
        edges.append((u,v))
    if len(set(edges))<k:return None
    sign*=(-1)**sum(edges[i]>edges[j] for i in range(k) for j in range(i+1,k))
    return tuple(sorted(edges)),sign


@lru_cache(None)
def graph_homotopy(q,graph):
    k=len(graph);assert k>=2
    partition=graph_partition(q,graph)
    out=defaultdict(int);count=0
    for i in range(k):
        for j in range(k):
            if i==j:continue
            for ei,ej in product((0,1),repeat=2):
                a,b,c,d=2*i+ei,2*i+1-ei,2*j+ej,2*j+1-ej
                count+=1
                for p,value in H_edge_exchange(partition,a,b,c,d).items():
                    projected=project_graph(p,k)
                    if projected:out[projected[0]]+=value*projected[1]
    assert count==4*k*(k-1)
    return {g:Q(c,2*count) for g,c in out.items() if c}


def check_graph(q,graph):
    out=defaultdict(Q)
    image=graph_homotopy(q,graph)
    for g,c in image.items():linear_add(out,normalized.differential(q-1,g),c)
    for g,c in normalized.differential(q,graph).items():linear_add(out,graph_homotopy(q+1,g),c)
    assert clean(out)=={graph:Q(1)},('graph contraction',q,graph,clean(out))
    return len(image)


def main():
    start=time.monotonic();partition_checks=0
    for n in range(1,6):
        for partition in ordered_partitions(n):
            got=compose_boundary_identity(partition,lambda p:H(p,0))
            expected=defaultdict(int,{partition:1});linear_add(expected,P(partition,0),-1)
            assert got==clean(expected),('one-letter homotopy',partition)
            partition_checks+=1
            if n>=2:
                got=compose_boundary_identity(partition,lambda p:H_transposition(p,0,1))
                expected=defaultdict(int,{partition:1});expected[rename(partition,0,1)]+=1
                assert got==clean(expected),('transposition homotopy',partition)
            if n>=4:
                got=compose_boundary_identity(partition,lambda p:H_edge_exchange(p,0,1,2,3))
                expected=defaultdict(int,{partition:1});expected[rename(rename(partition,0,2),1,3)]-=1
                assert got==clean(expected),('edge exchange homotopy',partition)
    print('ALL PARTITION IDENTITIES PASS',partition_checks,'SECONDS',time.monotonic()-start,flush=True)
    rng=random.Random(251070);records=[]
    for k in (2,3,4):
        checked=0;maximum=0;maximum_graph=None
        for q in range(1,2*k+1):
            graphs=normalized.basis(q,k)
            if k==4 and len(graphs)>25:graphs=rng.sample(graphs,25)
            for graph in graphs:
                count=check_graph(q,graph);checked+=1
                if count>maximum:maximum=count;maximum_graph=(q,graph)
        record=dict(exterior_degree=k,graphs_checked=checked,
                    complete=k<=3,max_primitive_terms=maximum,maximum_graph=maximum_graph)
        records.append(record)
        print('SPARSE GRAPH HOMOTOPY',record,'SECONDS',time.monotonic()-start,flush=True)
    # This must reproduce the independently computed unique k2 inverse.
    two_edge=[]
    for graph in normalized.basis(4,2):
        two_edge.append(dict(graph=graph,primitive=[[g,str(c)] for g,c in graph_homotopy(4,graph).items()]))
    result=dict(status='EXACT_SPARSE_PARTITION_AND_GRAPH_HOMOTOPY_CONTROLS',
                partition_checks=partition_checks,records=records,two_edge_inverse=two_edge,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start,
                scope='The displayed formulas have an algebraic uniform homotopy proof; these are exact finite convention controls. Polynomial primitive branching per input graph is not a total exponential network-width bound.')
    (HERE/'overnight_upper_ordered_sparse_homotopy.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
