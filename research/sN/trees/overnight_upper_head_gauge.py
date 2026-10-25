#!/usr/bin/env python3
"""Exact controls for head-subset closure inside an apex-star graph."""
from itertools import combinations,product
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def is_tree(n,edges):
    parent=list(range(n))
    def root(v):
        while parent[v]!=v:v=parent[v]
        return v
    for u,v in edges:
        a,b=root(u),root(v)
        if a==b:return False
        parent[a]=b
    return len(edges)==n-1

def vector(n,edge):return tuple(int(i==edge[0])-int(i==edge[1]) for i in range(n))

def main():
    records=[]
    for n in range(3,7):
        b=0;graph=tuple(sorted({(0,v) for v in range(1,n)}|{(v,v+1) for v in range(1,n-1)}))
        checked=trees=0
        for H in combinations(graph,n-1):
            if not is_tree(n,H):continue
            trees+=1
            for signs in product((1,-1),repeat=n-1):
                oriented=[e if s==1 else e[::-1] for e,s in zip(H,signs)]
                for bits in range(1,1<<(n-1)):
                    selected=[j for j in range(n-1) if bits>>j&1]
                    index=selected[0];u,v=oriented[index]
                    frozen=[oriented[j] for j in selected[1:]]
                    if v==b:root=u;head_sign=1
                    elif u==b:root=v;head_sign=-1
                    elif tuple(sorted((b,v))) not in H:
                        root=u;head_sign=1;frozen.append((b,v))
                    else:
                        assert tuple(sorted((b,u))) not in H
                        root=v;head_sign=-1;frozen.append((u,b))
                    free=[oriented[j] for j in range(n-1) if j not in selected]
                    frozen_undirected=[tuple(sorted(e)) for e in frozen]
                    free_undirected=[tuple(sorted(e)) for e in free]
                    assert len(set(frozen_undirected))==len(frozen_undirected)
                    assert not set(frozen_undirected)&set(free_undirected)
                    assert set(frozen_undirected+free_undirected)<=set(graph)
                    target=tuple(sum(vector(n,oriented[j])[i] for j in selected) for i in range(n))
                    actual=tuple(head_sign*(int(i==root)-int(i==b))+sum(vector(n,e)[i] for e in frozen) for i in range(n))
                    assert actual==target
                    checked+=1
        records.append(dict(labels=n,spanning_trees=trees,all_head_subset_orientation_checks=checked))
    cube_checks=0
    for m in range(1,7):
        for values in product((-1,0,1),repeat=m):
            total=0
            for mask in range(1,1<<m):
                pre=sum(v if mask>>i&1 else max(0,v) for i,v in enumerate(values))
                total+=(-1)**(mask.bit_count()+1)*max(0,pre)
            assert total==sum(max(0,v) for v in values)
            cube_checks+=1
    result=dict(status='EXACT_REFLECTED_APEX_STAR_HEAD_GAUGE_CONTROLS_PASSED',records=records,
        cube_identity_sign_checks=cube_checks,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Controls of the uniform tree/absent-star-edge proof and exact cube cover. The reflected five-state family is closed under this head gauge; no Hopf-product intertwining or all-N simplex identity is inferred.')
    (HERE/'overnight_upper_head_gauge.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'MEMBERSHIP_CHECKS',sum(r['all_head_subset_orientation_checks'] for r in records),'CUBE_CHECKS',cube_checks)

if __name__=='__main__':main()
