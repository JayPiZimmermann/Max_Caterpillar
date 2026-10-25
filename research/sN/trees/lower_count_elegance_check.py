#!/usr/bin/env python3
"""Small exact controls of the new global count; no numerical rank tests."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations,permutations,product
from pathlib import Path
import hashlib,json,math,time
HERE=Path(__file__).parent

def is_forest(n,edges):
    p=list(range(n))
    def root(x):
        while p[x]!=x:x=p[x]
        return x
    for u,v in edges:
        a,b=root(u),root(v)
        if a==b:return False
        p[a]=b
    return True

def block_checks():
    records=[]
    for n in (2,3):
        edges=[(i,i+1) for i in range(n-1)];best=[Q(0)]*(n+1)
        for signs in product((1,-1),repeat=n-1):
            oriented=[e if s==1 else e[::-1] for e,s in zip(edges,signs)]
            co=[Q(0)]*(n+1)
            for bits in range(1<<n):
                outside=[v for v in range(n) if not bits>>v&1]
                good=0
                for perm in permutations(outside):
                    pos={v:i for i,v in enumerate(perm)}
                    good+=all(pos[u]<pos[v] for u,v in oriented if u in pos and v in pos)
                co[bits.bit_count()]+=Q(good,math.factorial(len(outside)))
            best=[max(a,b) for a,b in zip(best,co)]
        expected=[Q(1,2),Q(2),Q(1)] if n==2 else [Q(1,3),Q(2),Q(3),Q(1)]
        assert best==expected
        records.append(dict(vertices=n,coefficients=list(map(str,best))))
    assert Q(53,24)**2 <= Q(7,4)**3
    assert Q(83,54)**2 <= Q(13,9)**3
    return records

def cross_size_check():
    n=4;possible=list(combinations(range(n),2));cases=ties=0
    for bits in range(1<<len(possible)):
        edges=[e for i,e in enumerate(possible) if bits>>i&1]
        if not is_forest(n,edges):continue
        adj=[set() for _ in range(n)]
        for u,v in edges:adj[u].add(v);adj[v].add(u)
        for kappa in product((-1,0,1,2),repeat=n):
            pendants={v for v in range(n) if len(adj[v])==1 and kappa[v]==0}
            phi={v for v in range(n) if adj[v] and v not in pendants}
            if any(len(adj[v]&phi)>2 for v in phi):continue
            encoded={};F=Q(0);F6=Q(0)
            for mask in range(1<<n):
                T={v for v in range(n) if mask>>v&1}
                if any(kappa[v]==0 and not(adj[v]&T) for v in T):continue
                outside=[v for v in range(n) if v not in T];good=0
                for order in permutations(outside):
                    higher=set(T);passes=True
                    for v in order:
                        if len(adj[v]&higher)!=kappa[v]:passes=False;break
                        higher.add(v)
                    good+=passes
                if not good:continue
                A=frozenset(T&phi)
                assert A not in encoded or encoded[A]==T
                encoded[A]=T;ties+=1
                a=Q(good,math.factorial(len(outside)))
                F+=a*Q(1,2)**len(T);F6+=a*Q(1,6)**len(T)
            assert F*F<=Q(7,4)**n
            assert F6<=1
            cases+=1
    return dict(labels=n,forest_kappa_cases=cases,passed_ties=ties,
                cross_size_injective=True,p_one_third_bound=True,y_one_sixth_bound=True)

def source_cover_check():
    cases=0
    for n in range(2,7):
        for word in product(range(n),repeat=n-2):
            degree=[1]*n
            for v in word:degree[v]+=1
            edges=[]
            for v in word:
                leaf=next(i for i,d in enumerate(degree) if d==1)
                edges.append((leaf,v));degree[leaf]-=1;degree[v]-=1
            edges.append(tuple(i for i,d in enumerate(degree) if d==1))
            adj=[set() for _ in range(n)]
            for u,v in edges:adj[u].add(v);adj[v].add(u)
            for r,s in product(range(n),repeat=2):
                kappa=[len(adj[v])-1+int(v==r)+int(v==s) for v in range(n)]
                pendants={v for v in range(n) if len(adj[v])==1 and kappa[v]==0}
                outleaves={v for v in range(n) if len(adj[v])==1 and kappa[v]==1}
                parent={r:None};stack=[r]
                for v in stack:
                    for w in adj[v]:
                        if w==parent[v]:continue
                        parent[w]=v;stack.append(w)
                chosen={tuple(sorted((v,w))) for v in outleaves for w in adj[v]}
                for v in range(n):
                    if len(adj[v])<=1 or adj[v]&(pendants|outleaves):continue
                    child=next(w for w in adj[v] if parent.get(w)==v)
                    chosen.add(tuple(sorted((v,child))))
                deg=Counter(v for e in chosen for v in e)
                assert max(deg.values(),default=0)<=2
                assert all(not(set(e)&pendants) for e in chosen)
                for v in range(n):
                    if v in pendants or deg[v]:continue
                    assert adj[v]&pendants or (len(adj[v])==1 and kappa[v] not in (0,1))
                cases+=1
    return dict(source_root_tree_cases=cases,maximum_cover_degree=2)

def main():
    started=time.monotonic()
    tails=[]
    for N,p,r in ((12,Q(1,4),3),(20,Q(1,4),5),(9,Q(1,3),3),(15,Q(1,3),5)):
        tail=1-sum(Q(math.comb(N,j))*p**j*(1-p)**(N-j) for j in range(r))
        assert tail>=Q(1,2)
        tails.append(dict(N=N,p=str(p),threshold=r,tail=str(tail)))
    out=dict(status='EXACT_SMALL_CONTROLS_PASS',blocks=block_checks(),
             cross_size=cross_size_check(),source_cover=source_cover_check(),tails=tails,
             seconds=time.monotonic()-started,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='Finite independent order enumeration and whole-stratum combinatorial controls. The uniform proof is in lower_count_elegance_routes.md; no Lean verification claimed.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
