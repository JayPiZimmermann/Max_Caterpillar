"""Finite structural control of the paired-collision matching/pole lemmas.

All unlabelled even trees on2,4,6,8vertices, every pairing, and (for nonzero
apex) every ordered choice of zero-frequency and unmatched-partner vertices.
No Fourier evaluator, rooted orientations, modular arithmetic, or producer DAG.
"""
from pathlib import Path
import json,time
import networkx as nx

def pairings(vertices):
    if not vertices:
        yield ()
        return
    a=vertices[0]
    for j in range(1,len(vertices)):
        b=vertices[j]
        for p in pairings(vertices[1:j]+vertices[j+1:]):yield ((a,b),)+p

def cuts(T):
    out=[]
    for a,b in T.edges:
        seen={a};stack=[a]
        while stack:
            u=stack.pop()
            for v in T[u]:
                if {u,v}=={a,b}:continue
                if v not in seen:seen.add(v);stack.append(v)
        out.append(seen)
    return out

def main():
    start=time.monotonic();counts={}
    for n in [2,4,6,8]:
        c0=c1=trees=0;record={}
        for T in nx.nonisomorphic_trees(n):
            trees+=1;nu=len(nx.max_weight_matching(T,maxcardinality=True));cs=cuts(T);vs=tuple(T.nodes)
            for pairs in pairings(vs):
                k=sum(all((a in C)==(b in C) for a,b in pairs) for C in cs)
                assert k<=nu-1
                assert (k==n//2-1)==all(T.has_edge(a,b) for a,b in pairs)
                c0+=1
            for zero in vs:
                for partner in vs:
                    if zero==partner:continue
                    rest=tuple(v for v in vs if v not in [zero,partner])
                    for pairs in pairings(rest):
                        k=sum(all((a in C)==(b in C) for a,b in pairs) for C in cs)
                        assert k<=nu+1 and k<=n//2
                        c1+=1
        counts[str(n)]={'tree_shapes':trees,'zero_apex_pairings':c0,'nonzero_apex_assignments':c1}
    result={'status':'FINITE_STRUCTURAL_POLE_CONTROLS_PASS','counts':counts,'seconds':time.monotonic()-start,'scope':'Finite controls only; uniform proofs are in overnight_uniform.md.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
