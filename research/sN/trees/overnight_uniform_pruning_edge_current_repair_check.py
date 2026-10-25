"""Independent exact head-exchange refutation of both root-slide repairs.

Enumerate slides as literal changes of oriented edges, rather than using
reachability or invariant kappa. Signed counts use all 120 orders.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,time

def key(head,E):return tuple(head),tuple(sorted(E))

def slides(head,E):
    first=key(head,E);seen={first};todo=[first]
    for (r,s),edges in todo:
        for i,(u,v)in enumerate(edges):
            rest=list(edges[:i]+edges[i+1:]);new=None
            if v==r:new=key((u,s),rest+[(v,u)])
            if u==s:new=key((r,v),rest+[(v,u)])
            if new is not None and new not in seen:seen.add(new);todo.append(new)
    return sorted(seen)

def score(head,E):
    r,s=head;all_edges=list(E)+[head];adj=[set()for _ in range(5)];out=[0]*5
    for u,v in all_edges:adj[u].add(v);adj[v].add(u);out[u]+=1
    J=[]
    for root in range(5):
        parent={root:None};todo=[root]
        for v in todo:
            for w in adj[v]:
                if w!=parent[v]:parent[w]=v;todo.append(w)
        val=0
        for p in itertools.permutations(range(5)):
            pos={v:i for i,v in enumerate(p)}
            if all(pos[v]>pos[w]for v,w in parent.items()if w is not None):val+=(-1)**sum(p[i]>p[j]for i in range(5)for j in range(i+1,5))
        J.append(val)
    assert sum(J)==0
    K=[5*out[v]*J[v]-sum(out[w]*J[w]for w in range(5))for v in range(5)]
    adj[r].remove(s);adj[s].remove(r);C={r};todo=[r]
    for v in todo:
        for w in adj[v]:
            if w not in C:C.add(w);todo.append(w)
    return sum(J[v]for v in C)*(K[r]-K[s])-sum(K[v]for v in C)*(J[r]-J[s])

def normalized(head,E):
    h=[0]*5;h[head[0]]+=1;h[head[1]]-=1;undirected=[]
    for u,v in E:
        undirected.append(tuple(sorted((u,v))))
        if u>v:h[u]+=1;h[v]-=1
    return tuple(h),tuple(sorted(undirected))

def main():
    start=time.monotonic();B=[(1,0),(1,2),(0,3),(3,4)];records=[]
    for i,H in enumerate(B):
        E=B[:i]+B[i+1:];states=slides(H,E);base=normalized(H,E)
        assert all(normalized(h,e)==base for h,e in states)
        qs=[score(h,e)for h,e in states];records.append({'head':H,'slide_states':states,'scores':qs,'sum':sum(qs),'count':len(states)})
    sums=[x['sum']for x in records];counts=[x['count']for x in records];assert sums==[4,-2,4,-3];assert counts==[3,1,4,3]
    assert sum(sums)==3;avg=sum(Q(x,c)for x,c in zip(sums,counts));assert avg==Q(-2,3)
    out={'status':'INDEPENDENT_EXACT_ROOT_SLIDE_REPAIR_REFUTATION','oriented_tree':B,'head_states':records,'sum_repair_head_exchange_defect':sum(sums),'average_repair_head_exchange_defect':str(avg),'scope':'Every state in each slide orbit is the same whole function. The single-head kernel sum is zero by the uniform head-exchange identity. Nonzero repaired score sums therefore refute both assignments on the full two-component kernel algebra.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='head_states'},indent=2))
if __name__=='__main__':main()
