#!/usr/bin/env python3
"""Geometric rank pruning and exact collinear aggregation of simplex lifts.

All internal-face support-function corrections are retained. Rank pruning is
only a top-class operation; this file does not claim an exact max network.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib,json,time
from flint import fmpz_mat
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_single_facet as single
import overnight_upper_ordered_undoubled as undoubled
import overnight_upper_triangle_attachments as attachment

HERE=Path(__file__).parent

@lru_cache(None)
def top_orientation(edges):
    n=len(edges[0]);parent=list(range(n))
    def root(v):
        while parent[v]!=v:v=parent[v]
        return v
    for e in edges:
        i=next(i for i,v in enumerate(e) if v>0)
        j=next(i for i,v in enumerate(e) if v<0)
        a,b=root(i),root(j)
        if a==b:return None
        parent[a]=b
    component=tuple(i for i in range(n) if root(i)!=root(0))
    assert component
    h=tuple(int(i==component[0])-int(i==0) for i in range(n))
    matrix=[[e[i] for e in edges]+[h[i]] for i in range(1,n)]
    det=int(fmpz_mat(matrix).det());assert det
    return component,1 if det>0 else -1

def support_chain(chain):
    result=defaultdict(int);dependent=zero_height=0
    for (h,edges),c in chain.items():
        orientation=top_orientation(edges)
        if orientation is None:dependent+=1;continue
        component,sign=orientation;height=sum(h[i] for i in component)
        if not height:zero_height+=1;continue
        result[(h,edges)]+=c*sign*(1 if height>0 else -1)
    return coherent.clean(result),dict(dependent_base_cubes=dependent,
                                      zero_height_cubes=zero_height)

def direction(edge):
    weight=next(v for v in edge if v>0)
    return tuple(v//weight for v in edge),weight

def merge_direction(chain,u):
    groups=defaultdict(list);untouched={}
    pivot=u.index(1)
    for (h,edges),c in chain.items():
        chosen=[(i,e,direction(e)[1]) for i,e in enumerate(edges) if direction(e)[0]==u]
        if not chosen:untouched[(h,edges)]=c;continue
        assert len(chosen)==1
        i,e,length=chosen[0];t=h[pivot]
        base=tuple(v-t*w for v,w in zip(h,u));rest=edges[:i]+edges[i+1:]
        groups[(base,rest)].append((t,t+length,c,(h,edges)))
    output=defaultdict(int,untouched);faces=defaultdict(int);merged=0
    for (base,rest),intervals in groups.items():
        changes=defaultdict(int);old_ends=defaultdict(int)
        for t,s,c,key in intervals:changes[t]+=c;changes[s]-=c;old_ends[s]+=c
        changes={t:c for t,c in changes.items() if c}
        active=0;previous=None;segments=[]
        for t,change in sorted(changes.items()):
            if previous is not None and active:segments.append((previous,t,active))
            active+=change;previous=t
        assert active==0
        if len(segments)>=len(intervals):
            for t,s,c,key in intervals:output[key]+=c
            continue
        merged+=len(intervals)-len(segments)
        new_ends=defaultdict(int)
        for t,s,c in segments:
            h=tuple(v+t*w for v,w in zip(base,u))
            e=tuple((s-t)*w for w in u)
            output[(h,tuple(sorted(rest+(e,))))]+=c
            new_ends[s]+=c
        # Exact valuation correction at every internal breakpoint.
        for t in set(old_ends)|set(new_ends):
            c=old_ends[t]-new_ends[t]
            if c:
                h=tuple(v+t*w for v,w in zip(base,u))
                faces[(h,rest)]+=c
    return coherent.clean(output),coherent.clean(faces),merged

def compress(chain,n):
    levels=defaultdict(lambda:defaultdict(int))
    for key,c in chain.items():levels[len(key[1])][key]+=c
    directions=[tuple(int(v==j)-int(v==i) for v in range(n))
                for i,j in combinations(range(n),2)]
    records=[]
    for degree in range(n-2,-1,-1):
        current=coherent.clean(levels[degree]);initial=len(current);merges=0
        for turn in range(3):
            changed=0
            for u in directions:
                current,faces,count=merge_direction(current,u)
                changed+=count
                for key,c in faces.items():levels[degree-1][key]+=c
            merges+=changed
            if not changed:break
        levels[degree]=current
        records.append(dict(base_dimension=degree,input_terms=initial,
                            output_terms=len(current),top_interval_reductions=merges))
    result={}
    for degree,chain in levels.items():
        assert degree>=0 or not chain
        result.update(coherent.clean(chain))
    return result,records

def value(chain,x):
    dot=lambda v:sum(a*b for a,b in zip(v,x))
    return sum(c*max(0,dot(h)+sum(max(0,dot(e)) for e in edges))
               for (h,edges),c in chain.items())

def main():
    start=time.monotonic();records=[]
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X,_=contraction.contract(coherent.delta({k:-v for k,v in triangle.items()},3),4)
    for dimension in (3,4,5,6):
        n=dimension+1
        top,pruning=support_chain(X)
        compressed,levels=compress(top,n)
        # Structured exact integer evaluations control coefficient/orientation conventions.
        controls=[tuple((i+seed)**2%11-5 for i in range(n)) for seed in range(7)]
        assert all(value(top,x)==value(compressed,x) for x in controls)
        record=dict(simplex_dimension=dimension,formal_cubes=len(X),
                    top_pyramids=len(top),compressed_all_dimensions=len(compressed),
                    compressed_top_pyramids=levels[0]['output_terms'],levels=levels,
                    pruning=pruning,max_generator_length=max(
                        (max(e) for h,edges in compressed for e in edges),default=0),
                    exact_integer_value_controls=len(controls))
        records.append(record)
        print('ACTUAL GEOMETRIC COMPRESSION',record,'SECONDS',time.monotonic()-start,flush=True)
        receipt=dict(status='BOUNDED_ACTUAL_SIMPLEX_GEOMETRIC_COMPRESSION',
                     records=records,seconds=time.monotonic()-start,
                     producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                     scope='Compression retains every internal-face correction exactly. Initial rank pruning and the original simplex lift only specify a top-class identity; this is not yet an exact max network or a uniform width theorem.')
        (HERE/'overnight_upper_ordered_geometric_compress.json').write_text(json.dumps(receipt,indent=2)+'\n')
        if dimension==6:break
        fixed,boundary,_=undoubled.correction(X,n)
        X,_=contraction.contract(single.coface(fixed,n,0),n+1)
        assert coherent.boundary(X)==boundary

if __name__=='__main__':main()
