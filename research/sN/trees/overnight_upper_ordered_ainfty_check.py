#!/usr/bin/env python3
"""Compact independent replay of the complete two-page A-infinity obstruction.

Uses half-edge partition splitting instead of the producer's edge differential,
and exhaustive two-colour assignments instead of its crossing-graph BFS.
No large matrix or original RREF is required.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib,json,time
from flint import fmpq_mat

HERE=Path(__file__).parent

def decode(terms):return {tuple(map(tuple,g)):Q(c) for g,c in terms}
def clean(chain):return {g:c for g,c in chain.items() if c}

def add(*weighted):
    out=defaultdict(Q)
    for scale,chain in weighted:
        for g,c in chain.items():out[g]+=scale*c
    return clean(out)

def basis(q,k):
    return [g for g in combinations(combinations(range(q),2),k)
            if set(sum((list(e) for e in g),[]))==set(range(q))]

def two_pages(g):
    def cross(e,f):
        a,b=e;c,d=f
        return a<c<b<d or c<a<d<b
    crossings=[(i,j) for i,j in combinations(range(len(g)),2) if cross(g[i],g[j])]
    return any(all(bits[i]!=bits[j] for i,j in crossings)
               for bits in product((0,1),repeat=len(g)))

def delta_graph(q,g):
    blocks=[[] for _ in range(q)]
    for i,(u,v) in enumerate(g):blocks[u].append(2*i);blocks[v].append(2*i+1)
    out=defaultdict(int)
    for i,block in enumerate(blocks):
        for bits in product((0,1),repeat=len(block)):
            if len(set(bits))<2:continue
            left=[a for a,b in zip(block,bits) if b==0]
            right=[a for a,b in zip(block,bits) if b==1]
            partition=blocks[:i]+[left,right]+blocks[i+1:]
            positions={a:j for j,b in enumerate(partition) for a in b}
            edges=[];sign=(-1)**(i+1)
            for j in range(len(g)):
                u,v=positions[2*j],positions[2*j+1]
                if u==v:break
                if u>v:u,v=v,u;sign=-sign
                edges.append((u,v))
            else:
                if len(set(edges))<len(edges):continue
                sign*=(-1)**sum(edges[a]>edges[b] for a,b in combinations(range(len(edges)),2))
                out[tuple(sorted(edges))]+=sign
    return clean(out)

def delta(q,chain):
    out=defaultdict(Q)
    for g,c in chain.items():
        for h,v in delta_graph(q,g).items():out[h]+=c*v
    return clean(out)

def mul(a,b,q):
    out=defaultdict(Q)
    for g,c in a.items():
        for h,d in b.items():out[g+tuple((u+q,v+q) for u,v in h)]+=c*d
    return clean(out)

def matrix_rank(columns,rows):
    return fmpq_mat([[str(c.get(g,0)) for c in columns] for g in rows]).rank()

def main():
    start=time.monotonic();path=HERE/'overnight_upper_ordered_ainfty_affine.json'
    data=json.loads(path.read_text())
    assert data['status']=='EXACT_COMPLETE_AFFINE_TWO_PAGE_FIFTH_PRIMITIVE_FAILURE'
    E={((0,1),):Q(1)}
    H2,H3,H4=(decode(data[f'H{i}']) for i in (2,3,4))
    K3=[decode(c) for c in data['H3_kernel']]
    K4=[decode(c) for c in data['H4_kernel']]
    lifts=[decode(c) for c in data['H4_lifts']]
    assert delta(3,H2)==add((-1,mul(E,E,2)))
    assert delta(4,H3)==add((-1,mul(E,H2,2)),(1,mul(H2,E,3)))
    def fourth(h3):
        return add((-1,mul(E,h3,2)),(1,mul(H2,H2,3)),(-1,mul(h3,E,4)))
    assert delta(5,H4)==fourth(H3)
    records=[]
    for k,kernels in ((2,[]),(3,K3),(4,K4)):
        source=[g for g in basis(k+1,k) if two_pages(g)]
        target=basis(k+2,k)
        columns=[delta_graph(k+1,g) for g in source]
        rank=matrix_rank(columns,target)
        assert all(not delta(k+1,c) for c in kernels)
        krank=matrix_rank(kernels,source) if kernels else 0
        assert krank==len(kernels)==len(source)-rank
        assert all(set(c)<=set(source) for c in kernels)
        records.append(dict(k=k,columns=len(source),rank=rank,complete_kernel=len(kernels)))
    assert len(K3)==len(lifts)==1 and len(K4)==15
    for c,lift in zip(K3,lifts):
        assert delta(5,lift)==add((-1,mul(E,c,2)),(-1,mul(c,E,4)))
    def fifth(h3,h4):
        return add((-1,mul(E,h4,2)),(1,mul(H2,h3,3)),
                   (-1,mul(h3,H2,4)),(1,mul(h4,E,5)))
    target=fifth(H3,H4)
    assert target==decode(data['target'])
    assert not delta(7,target)
    separator=decode(data['separator'])
    pairing=lambda c:sum(v*c.get(g,0) for g,v in separator.items())
    fifth_source=[g for g in basis(6,5) if two_pages(g)]
    assert len(fifth_source)==1509
    assert all(pairing(delta_graph(6,g))==0 for g in fifth_source)
    variations=[fifth(c,lift) for c,lift in zip(K3,lifts)]+[fifth({},c) for c in K4]
    assert all(pairing(c)==0 for c in variations)
    assert pairing(target)==1
    result=dict(status='INDEPENDENT_EXACT_COMPLETE_AFFINE_TWO_PAGE_OBSTRUCTION',
                lower_coverage=records,all_fifth_graphs=len(basis(6,5)),
                two_page_fifth_graphs=len(fifth_source),gauge_directions=len(variations),
                separator_terms=len(separator),target_pairing='1',
                certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start)
    (HERE/'overnight_upper_ordered_ainfty_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
