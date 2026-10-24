#!/usr/bin/env python3
"""Compact finite witness with explicit BFS and canonical-head membership.

The exporter is not an exact identity gate. The replay reconstructs every
selected function from small combinatorial witnesses, uses direct DFS cuts,
and compares its entire rational expression with the controlled native-engine
decoder. No large sampled matrix is needed for this replay.
"""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import sys
import time

import overnight_upper_modular_exact as E
from exponential_families import breadth_first,normalize
from cycle_fourier import canonical,permute

HERE=Path(__file__).parent
OUTPUT=HERE/'overnight_upper_affine_certificate_7.json'


def group(n):return [tuple((a*i+b)%n for i in range(n)) for a in range(n) if math.gcd(a,n)==1 for b in range(n)]


def graphs(n):
    result={};m=n-1
    for tree in breadth_first(m):
        degrees=[0]*m
        for u,v in tree:degrees[u]+=1
        for shift,sign,a,b in product(range(m),(-1,1),range(1,n),range(n)):
            if math.gcd(a,n)>1:continue
            pi=[b]+[(a*(1+(sign*i+shift)%m)+b)%n for i in range(m)]
            edges=normalize((pi[u+1],pi[v+1]) for u,v in tree)
            result.setdefault((pi[0],edges),dict(degrees=degrees,shift=shift,sign=sign,a=a,b=b))
    return result


def root_witness(key):
    h,edges=key;n=len(h);vertices={v for e in edges for v in e};apex,=set(range(n))-vertices
    for root in sorted(vertices):
        base=[0]*n;base[apex]=-1;base[root]=1
        for mask in range(1<<len(edges)):
            hh=base.copy()
            for j,(u,v) in enumerate(edges):
                if mask>>j&1:hh[u]-=1;hh[v]+=1
            if tuple(hh)==tuple(h):return dict(root=root,orientation_mask=mask)
    raise AssertionError('noncanonical head')


def export():
    started=time.monotonic();family=json.loads(E.FAMILY.read_text());crt=json.loads(E.CRT.read_text())
    domain=graphs(7);assert len(domain)==6216
    graph_index={};witnesses=[];records=[]
    for col,c in zip(crt['selected_columns'],crt['coefficients']):
        orbit=family['orbits'][col];head,edges=orbit[0];edges=tuple(map(tuple,edges))
        vertices={v for e in edges for v in e};apex,=set(range(7))-vertices;g=(apex,edges)
        assert g in domain
        if g not in graph_index:
            graph_index[g]=len(witnesses);witnesses.append(dict(apex=apex,edges=edges,**domain[g]))
        records.append(dict(head=head,graph=graph_index[g],coefficient=c,orbit_size=len(orbit),
                            original_column=col,**root_witness((head,edges))))
    out=dict(status='EXPLICIT_RATIONAL_PROPOSAL_PENDING_EXACT_GATE',n=7,
             group='Aff(Z/7Z)',graph_witnesses=witnesses,orbit_records=records,
             source_solution_sha256=E.base.digest(E.CRT),source_family_sha256=E.base.digest(E.FAMILY),
             producer_sha256=E.base.digest(Path(__file__)),selected_units=sum(r['orbit_size'] for r in records),
             elapsed_seconds=time.monotonic()-started)
    OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('EXPORTED',len(records),'ORBITS',len(witnesses),'GRAPH WITNESSES',OUTPUT.stat().st_size,'BYTES',flush=True)


def checked_orbits(data):
    n=data['n'];m=n-1;gs=[]
    for witness in data['graph_witnesses']:
        degrees=witness['degrees'];assert len(degrees)==m and sum(degrees)==m-1
        assert all(isinstance(x,int) and x>=0 for x in degrees)
        edges=[];assigned=1
        for u,degree in enumerate(degrees):
            assert assigned>u
            edges.extend((u,v) for v in range(assigned,assigned+degree));assigned+=degree
        assert assigned==m
        shift,sign,a,b=(witness[k] for k in ('shift','sign','a','b'))
        assert 0<=shift<m and sign in (-1,1) and 0<a<n and math.gcd(a,n)==1 and 0<=b<n
        pi=[b]+[(a*(1+(sign*i+shift)%m)+b)%n for i in range(m)]
        graph=normalize((pi[u+1],pi[v+1]) for u,v in edges)
        assert witness['apex']==pi[0] and graph==tuple(map(tuple,witness['edges']))
        gs.append((pi[0],graph))
    permutations=group(n);orbits=[];seen=set()
    for record in data['orbit_records']:
        apex,edges=gs[record['graph']];root=record['root'];mask=record['orientation_mask']
        assert root in set(range(n))-{apex} and 0<=mask<1<<(n-2)
        head=[0]*n;head[apex]=-1;head[root]=1
        for j,(u,v) in enumerate(edges):
            if mask>>j&1:head[u]-=1;head[v]+=1
        assert head==record['head'];key=(tuple(head),edges)
        orbit=tuple(sorted({permute(key,pi) for pi in permutations}))
        assert len(orbit)==record['orbit_size'] and orbit[0] not in seen
        seen.add(orbit[0]);orbits.append(orbit)
    assert sum(map(len,orbits))==data['selected_units']
    return orbits


def expression(data):
    n=data['n'];orbits=checked_orbits(data);out=defaultdict(Q);cache={};form_cache={}
    one=(0,)*(n-1)+(1,)
    def form(raw):
        raw=tuple(raw)
        if raw not in form_cache:
            f=tuple(x-raw[-1] for x in raw[:-1])+(0,);g=math.gcd(*f)
            if next(x for x in f if x)<0:g=-g
            form_cache[raw]=(g,tuple(x//g for x in f))
        return form_cache[raw]
    for record,orbit in zip(data['orbit_records'],orbits):
        coeff=Q(record['coefficient'])
        for head,edges in orbit:
            if edges not in cache:
                vertices={v for e in edges for v in e};apex,=set(range(n))-vertices;sides=[]
                for u,v in edges:
                    reached={u};todo=[u]
                    while todo:
                        w=todo.pop()
                        for x,y in edges:
                            if (x,y)==(u,v):continue
                            z=y if x==w else x if y==w else None
                            if z is not None and z not in reached:reached.add(z);todo.append(z)
                    assert v not in reached;sides.append(tuple(sorted(reached)))
                cache[edges]=(apex,sides)
            apex,sides=cache[edges];den=Counter();scale=coeff
            for side in sides:
                H=sum(head[i] for i in side)
                for shift in (H,H+1):
                    g,f=form([int(i in side)+shift*int(i==apex) for i in range(n)])
                    scale/=g;den[f]+=1
            s,num=form([-int(i==apex) for i in range(n)]);power=n-4;scale*=s**power
            cancel=min(power,den[num]);power-=cancel;den[num]-=cancel
            key=(num if power else one,power,tuple(sorted((f,p) for f,p in den.items() if p)))
            out[key]+=scale
    for key,c in E.exact_expression(n,[],[]).items():out[key]+=c
    return {k:c for k,c in out.items() if c}


def replay():
    started=time.monotonic();data=json.loads(OUTPUT.read_text());direct=expression(data)
    native,controls=E.build(json.loads(E.CRT.read_text()),controls=False)
    assert direct==native
    h=hashlib.sha256()
    for term,c in sorted(direct.items()):h.update(repr((term,str(c))).encode());h.update(b'\n')
    out=dict(status='COMPLETE_DIRECT_DFS_EXPRESSION_REPLAY_PASS',certificate_sha256=E.base.digest(OUTPUT),
             producer_sha256=E.base.digest(Path(__file__)),expression_sha256=h.hexdigest(),
             exact_terms=len(direct),selected_units=data['selected_units'],elapsed_seconds=time.monotonic()-started)
    (HERE/'overnight_upper_affine_replay_7.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps(out),flush=True)


if __name__=='__main__':globals()[sys.argv[1]]()
