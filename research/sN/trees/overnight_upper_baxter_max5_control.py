#!/usr/bin/env python3
"""Convert the independently known max5 network to graphic forest atoms.

Negative inner coefficients and length-two segments are removed by exact
scalar identities before geometric tiling. The full residual is then checked
by rational principal parts. This is a control, not a new uniform formula.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations,product
from pathlib import Path
import hashlib,json,sys,time
import overnight_upper_baxter_apex_geometry as geom
import overnight_upper_baxter_forest_states as family
from overnight_upper_baxter_apex_probe import atom_term
HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import Verifier,term

def clean(d):return {k:v for k,v in d.items() if v}
def shifted(h,e,w=1):return tuple(a+w*b for a,b in zip(h,e))

@lru_cache(None)
def expand(head,features):
    """Exact scalar expansion to positive unit-length comparison functions."""
    for i,(edge,w) in enumerate(features):
        rest=features[:i]+features[i+1:]
        if w<0:
            branches=[(head,rest,1),(shifted(head,edge,w),rest,1),
                      (head,tuple(sorted(rest+((tuple(-x for x in edge),-w),))),-1)]
            break
        if w>1:
            assert w==2
            unit=tuple(sorted(rest+((edge,1),)))
            branches=[(head,unit,1),(shifted(head,edge),unit,1),
                      (shifted(head,edge),rest,-1)]
            break
    else:
        h=head;edges=[]
        for e,w in features:
            assert w==1
            u=e.index(1);v=e.index(-1)
            if u>v:h=shifted(h,e);u,v=v,u
            edges.append((u,v))
        return { (h,tuple(sorted(edges))):Q(1) }
    output=defaultdict(Q)
    for h,fs,c in branches:
        for key,value in expand(h,fs).items():output[key]+=c*value
    return clean(output)

def graph_components(n,edges):
    remaining=set(range(n));out=[]
    while remaining:
        stack=[min(remaining)];seen={stack[0]}
        while stack:
            u=stack.pop()
            for a,b in edges:
                if a==u and b not in seen:seen.add(b);stack.append(b)
                if b==u and a not in seen:seen.add(a);stack.append(a)
        out.append(tuple(sorted(seen)));remaining-=seen
    return out

@lru_cache(None)
def tiles(n,graph):
    components=graph_components(n,graph);assert len(components)==2
    result=[]
    for basis in combinations(graph,n-2):
        if geom.components(n,basis) is None:continue
        potential={min(c):0 for c in components}
        while len(potential)<n:
            for u,v in basis:
                height=1<<graph.index((u,v))
                if u in potential and v not in potential:potential[v]=potential[u]-height
                elif v in potential and u not in potential:potential[u]=potential[v]+height
        shift=[0]*n
        for u,v in graph:
            if (u,v) in basis:continue
            slack=potential[u]-potential[v]-(1<<graph.index((u,v)))
            assert slack
            if slack>0:shift[u]+=1;shift[v]-=1
        result.append((tuple(shift),basis))
    return result

def geometric_forest_terms(n,head,graph):
    components=graph_components(n,graph)
    if len(components)>2:return {}
    result=defaultdict(Q)
    if len(components)==2:
        if not sum(head[i] for i in components[0]):return {}
        for shift,basis in tiles(n,graph):result[(geom.addv(head,shift),basis)]+=1
    else:
        for mask,fixed,subtiles in geom.facets(n,graph):
            h=geom.addv(head,fixed)
            if sum(h[i] for i in range(n) if mask>>i&1)>=0:continue
            for shift,basis in subtiles:result[(geom.addv(h,shift),basis)]+=1
    return clean(result)

def value(units,x):
    dot=lambda v:sum(a*b for a,b in zip(v,x))
    return sum(c*max(0,dot(h)+sum(max(0,x[u]-x[v]) for u,v in edges))
               for (h,edges),c in units.items())

def main():
    start=time.monotonic();n=5
    path=HERE.parent/'best5/overnight_fixed_cross_net9_18.json'
    network=json.loads(path.read_text());features=list(map(tuple,network['first_layer']))
    weights=[list(map(Q,row)) for row in network['second_layer']]
    outputs=list(map(Q,network['output']))
    assert weights[1]==[-v for v in weights[0]] and outputs[:2]==[1,-1]
    assert all(not any(row[7:]) for row in weights[2:])
    units=defaultdict(Q)
    for row,output in zip(weights[2:],outputs[2:]):
        fs=tuple(sorted((e,int(w)) for e,w in zip(features[:7],row[:7]) if w))
        assert all(w==int(w) for w in row)
        for key,c in expand((0,)*n,fs).items():units[key]+=output*c
    units=clean(units)
    # Exact scalar expansion controls, retaining the first shallow pair.
    controls=0
    for x in product((-1,0,1),repeat=n):
        f=[max(0,sum(a*b for a,b in zip(e,x))) for e in features]
        shallow=sum(a*b for a,b in zip(weights[0],f))
        original=sum(output*max(0,sum(a*b for a,b in zip(row,f)))
                     for row,output in zip(weights,outputs))
        assert original==max(x)
        assert value(units,x)+shallow==original
        controls+=1
    forests=defaultdict(Q)
    for (head,graph),coefficient in units.items():
        for key,c in geometric_forest_terms(n,head,graph).items():forests[key]+=coefficient*c
    forests=clean(forests)
    residual=defaultdict(Q)
    for (head,basis),coefficient in forests.items():
        atom=family.forest_atom(n,basis,head);assert atom is not None
        key,c=atom_term(n,atom);residual[key]+=coefficient*c
    residual=clean(residual)
    target_key,target_c=term(1,(0,0,0,0,1),0,
        [(((-1,)*4+(0,)) if i==0 else tuple(int(j==i-1) for j in range(4))+(0,),1) for i in range(5)])
    residual[target_key]=residual.get(target_key,Q(0))-target_c
    verifier=Verifier(budget=150)
    assert verifier.check(clean(residual)),'exact max5 rational-function residual'
    graph=((0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,4),(3,4))
    heads={basis:family.head_family(n,graph,basis) for basis in combinations(graph,3)
           if geom.components(n,basis) is not None}
    exact_members=[];reflected=[];outside=[]
    for (head,basis),coefficient in forests.items():
        if head in heads[basis]:exact_members.append((head,basis,coefficient));continue
        reflected_head=tuple(-head[i]-sum(int(i==u)-int(i==v) for u,v in basis) for i in range(n))
        if reflected_head in heads[basis]:reflected.append((head,basis,coefficient));continue
        outside.append((head,basis,coefficient))
    receipt=dict(status='EXACT_KNOWN_MAX5_GRAPHIC_FOREST_CONTROL',labels=n,
        positive_unit_length_units=len(units),nonzero_geometric_forests=len(forests),
        exact_first_family_members=len(exact_members),reflected_first_family_members=len(reflected),
        outside_first_family=len(outside),outside_examples=[dict(head=h,edges=b,coefficient=str(c)) for h,b,c in outside[:8]],
        forests=[dict(head=h,edges=b,coefficient=str(c)) for (h,b),c in sorted(forests.items())],
        principal_part_calls=verifier.calls,integer_scalar_controls=controls,
        source_network_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        evaluator_sha256=hashlib.sha256((HERE/'overnight_upper_baxter_apex_geometry.py').read_bytes()).hexdigest(),
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
        scope='Known exact max5 network converted by exact scalar identities and graphic tiling. This independently controls the Fourier evaluator atN5; no new all-N upper bound or whole-function forest identity is claimed.')
    (HERE/'overnight_upper_baxter_max5_control.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status'],'UNITS',len(units),'FORESTS',len(forests),'MEMBERS',len(exact_members),
          'REFLECTED',len(reflected),'OUTSIDE',len(outside),'SECONDS',receipt['seconds'],flush=True)

if __name__=='__main__':main()
