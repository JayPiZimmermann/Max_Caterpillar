"""Bounded exact descent gate for a two-root signed-extension assignment.

Gamma(U)=sum_{v<w in A}(-1)^dist(v,w) I(T,v)I(T,w), where A is the
positive-edge component of the canonical root and I is rooted-poset imbalance.
The assignment is a candidate, not a claimed rational-kernel invariant.
All26 five-label root/orientation orbits; exact evaluation-functional solve.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,time
import networkx as nx
import sympy as S
from dfs_review_fourier import family,orbit_exact,points
from overnight_uniform_pruning_signbalance import extensions
from overnight_uniform_pruning_infinity import rooted_cuts

HERE=Path(__file__).parent

def gamma(unit,n):
    T=nx.Graph(unit['edges']);vertices=sorted(T);I={}
    for v in vertices:
        parent={v:None};todo=[v];E=[]
        for x in todo:
            for y in T[x]:
                if y!=parent[x]:parent[y]=x;todo.append(y);E.append((x-1,y-1))
        I[v]=extensions(n-1,E)[1]
    positive=nx.Graph();positive.add_nodes_from(vertices)
    for e,(_,sign) in zip(unit['edges'],rooted_cuts(unit)):
        if sign==1:positive.add_edge(*e)
    A=sorted(nx.node_connected_component(positive,unit['root']))
    value=sum((-1)**nx.shortest_path_length(T,v,w)*I[v]*I[w] for v,w in itertools.combinations(A,2))
    return value,{'root_component':A,'signed_root_counts':I}

def main():
    start=time.monotonic();n=5;units=family(n,'all');perms=list(itertools.permutations(range(n)));pts=list(points(n,30));rows=[];metadata=[];values=[]
    for u in units:
        v,m=gamma(u,n);values.append(v);metadata.append(m)
    for pt in pts:rows.append([orbit_exact(u,pt,n,perms) for u in units]+[Q(1, __import__('math').prod(pt))])
    E=S.Matrix(rows);A=E[:,:-1];desired=S.Matrix(values);rank=A.rank();aug=A.col_join(S.Matrix([values])).rank();result={'status':'EXACT_SIGNED_ASSIGNMENT_DESCENT_GATE','arity':5,'ordinary_rank':rank,'with_assignment_rank':aug,'units':units,'assignment':values,'assignment_metadata':metadata,'points':pts,'rows':[[str(x) for x in r] for r in rows]}
    if rank==aug:
        w,pars=A.T.gauss_jordan_solve(desired);w=w.subs({p:0 for p in pars});assert A.T*w==desired
        result['weights']=list(map(str,w));result['target_response']=str((w.T*E[:,-1])[0]);result['scope']='Exact evaluation functional realizes Gamma on every5-label orbit; no uniform theorem.'
    else:
        rel=next(v for v in A.nullspace() if(desired.T*v)[0]);result['finite_relation']=list(map(str,rel));result['assignment_pairing']=str((desired.T*rel)[0]);result['scope']='Candidate fails to descend on the tested exact grid. The saved relation needs a rational-function identity check before this becomes an exact invariant refutation.'
    result['seconds']=time.monotonic()-start
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],rank,aug,result.get('target_response','inconsistent'),result['seconds'],flush=True)
if __name__=='__main__':main()
