"""Independent elementary check refuting the complete-Laplacian score.

No saved grid, graph library, signed-subset DP, or kernel routine is imported.
The functions coincide after an explicit permutation and one ReLU identity.
Signed extension counts are recomputed by all 120 vertex orders.
"""
from pathlib import Path
import itertools,json,time

UNITS=[{'root':1,'edges':[(2,1),(3,1),(2,4)]},
       {'root':1,'edges':[(2,1),(1,3),(4,2)]}]

def normalized(unit,p):
    h=[0]*5;h[p[unit['root']]]+=1;h[p[0]]-=1;E=[]
    for u,v in unit['edges']:
        u,v=p[u],p[v];E.append(tuple(sorted((u,v))))
        if u>v:h[u]+=1;h[v]-=1
    return h,sorted(E)

def current_score(unit):
    E=unit['edges']+[(unit['root'],0)];adj=[[]for _ in range(5)];k=[0]*5
    for u,v in E:adj[u].append(v);adj[v].append(u);k[u]+=1
    J=[]
    for r in range(5):
        parent={r:None};queue=[r]
        for v in queue:
            for w in adj[v]:
                if w!=parent[v]:parent[w]=v;queue.append(w)
        z=0
        for p in itertools.permutations(range(5)):
            pos={v:i for i,v in enumerate(p)}
            if all(pos[v]>pos[w]for v,w in parent.items()if w is not None):
                z+=(-1)**sum(p[i]>p[j]for i in range(5)for j in range(i+1,5))
        J.append(z)
    return J[0]*sum(x*y for x,y in zip(k,J)),J,k

def main():
    start=time.monotonic();p=(0,2,1,4,3);lhs=normalized(UNITS[0],p);rhs=normalized(UNITS[1],range(5));assert lhs==rhs
    scores=[current_score(u)for u in UNITS];assert [x[0]for x in scores]==[-1,0]
    out={'status':'INDEPENDENT_EXACT_HEAD_CURRENT_REFUTATION','units':UNITS,'permutation':p,'common_normalized_head':lhs[0],'common_undirected_edges':lhs[1],'scores':[{'score':q,'J':J,'outdegree':k}for q,J,k in scores],'identity':'x_2+sigma(x_1-x_2)=x_1+sigma(x_2-x_1)','scope':'The proposed score is not invariant even under equality of whole functions after a label permutation. This refutes this score, not a matching separator.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
