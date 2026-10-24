"""Exact controls for a full-symmetry pair-at-infinity recursion.

Direct side: normalized heads, positive-endpoint cuts, leading coefficients.
Recursion side: rooted-away cuts, marked edge contraction, rooted-tree hook
counts. No shared cut convention between the two evaluations. Fraction only.
All5-label canonical rooted/oriented orbits, plus structured7/9-label units.
Bounded phase120seconds, one thread. No separation claim.
"""
from fractions import Fraction as Q
from pathlib import Path
import itertools,json,math,time,sys
import networkx as nx
from dfs_review_fourier import family

HERE=Path(__file__).parent

def sides(edges,positive):
    adj={v:set() for e in edges for v in e}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    out=[]
    for u,v in positive:
        seen={u};todo=[u]
        while todo:
            x=todo.pop()
            for y in adj[x]:
                if (x==u and y==v) or (x==v and y==u):continue
                if y not in seen:seen.add(y);todo.append(y)
        out.append(seen)
    return out

def normal_factors(unit,n):
    edges=[tuple(sorted(e)) for e in unit['edges']]
    head=[-1]+[0]*(n-1);head[unit['root']]+=1
    for u,v in unit['edges']:
        if u>v:head[u]+=1;head[v]-=1
    return [(C,sum(head[i] for i in C)) for C in sides(edges,edges)]

def direct(unit,xi):
    n=len(xi)+2;fac=normal_factors(unit,n);base=[0,-sum(xi)]+xi;slope=[1,-1]+[0]*len(xi)
    finite=Q(0);infinite=Q(0);counts=[0,0]
    for p in itertools.permutations(range(n)):
        b=[base[i] for i in p];d=[slope[i] for i in p];ad=n-4 if d[0] else 0
        num=(-d[0] if d[0] else -b[0])**(n-4);den=1;dd=0
        for C,h in fac:
            q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
            for k in [h,h+1]:
                c=q0+k*b[0];t=q1+k*d[0]
                if t:dd+=1;den*=t
                else:assert c;den*=c
        assert ad-dd<=-2,(unit,p,ad,dd)
        if ad-dd==-2:
            value=Q(num,den)
            if d[0]:infinite+=value;counts[1]+=1
            else:finite+=value;counts[0]+=1
    return finite,infinite,counts

def rooted_cuts(unit):
    vertices={v for e in unit['edges'] for v in e};out=[]
    for C in sides(unit['edges'],unit['edges']):
        if unit['root'] in C:out.append((vertices-C,-1))
        else:out.append((C,1))
    return out

def orbit_boundary(unit,merged,xi):
    n=len(xi)+1;cuts=rooted_cuts(unit);slots=[i for i in range(n) if i!=merged];total=Q(0)
    for vals in itertools.permutations(xi):
        w=[0]*n;w[merged]=-sum(xi)
        for i,x in zip(slots,vals):w[i]=x
        a=w[0];den=1
        for C,eps in cuts:
            q=sum(w[i] for i in C);den*=q*(q+eps*a)
        assert den
        total+=Q((-a)**(n-3),den) # (-a)*kernel at arity n
    return total

def contract(unit,edge,n):
    keep,drop=sorted(edge);vertices=[i for i in range(n) if i!=drop];ren={v:i for i,v in enumerate(vertices)}
    def image(v):return ren[keep if v==drop else v]
    E=[(image(u),image(v)) for u,v in unit['edges'] if {u,v}!=set(edge)]
    return {'root':image(unit['root']),'edges':E},image(keep)

def contamination(unit,n):
    G=nx.Graph(unit['edges']);root=unit['root'];prod=math.prod(eps for _,eps in rooted_cuts(unit));reachable={root};todo=[root]
    # Along an eligible root-to-v path, the positive endpoint is farther from root.
    children={v:[] for v in G}
    for u,v in unit['edges']:children[v].append(u)
    while todo:
        v=todo.pop()
        for u in children[v]:
            if u not in reachable:reachable.add(u);todo.append(u)
    hooks={}
    for v in reachable:
        parent={v:None};order=[v]
        for x in order:
            for y in G[x]:
                if y!=parent[x]:parent[y]=x;order.append(y)
        size={x:1 for x in G}
        for x in reversed(order[1:]):size[parent[x]]+=size[x]
        denominator=math.prod(size[x] for x in G if x!=v)
        assert math.factorial(n-2)%denominator==0
        hooks[v]=math.factorial(n-2)//denominator
    return prod*sum(hooks.values()),hooks

def check(unit,xi):
    n=len(xi)+2;f,i,c=direct(unit,xi);C,hooks=contamination(unit,n)
    expected_i=Q(2*(-1)**n*C,math.prod(xi));bs=[]
    for edge in unit['edges']:
        u,v=contract(unit,edge,n);bs.append(orbit_boundary(u,v,xi))
    expected_f=2*sum(bs)
    assert i==expected_i,(unit,'infinity',i,expected_i)
    assert f==expected_f,(unit,'finite',f,expected_f)
    return {'arity':n,'unit':unit,'xi':xi,'finite_apex_part':str(f),'infinite_apex_part':str(i),'total':str(f+i),'contamination_integer':C,'reachable_hook_counts':hooks,'contraction_values':list(map(str,bs)),'surviving_assignments':c}

def main():
    start=time.monotonic();mode=sys.argv[1] if len(sys.argv)>1 else 'small';rows=[]
    if mode=='small':
        for u in family(5,'all'):
            rows.append(check({'root':u['root'],'edges':u['edges']},[1,3,9]))
        E=[(1,2),(2,3),(3,4),(4,5),(3,6)]
        for root,rev in [(1,False),(3,True),(6,False)]:
            rows.append(check({'root':root,'edges':[(v,u) if rev else (u,v) for u,v in E]},[1,3,9,27,81]))
    elif mode=='claw9':
        E=[(1,2),(1,3),(3,4),(4,5),(1,6),(6,7),(7,8)]
        rows.append(check({'root':1,'edges':E},[1,3,9,27,81,243,729]))
    else:raise ValueError(mode)
    result={'status':'EXACT_PAIR_INFINITY_RECURSION_CONTROLS_PASS','mode':mode,'checked_units':len(rows),'rows':rows,'seconds':time.monotonic()-start,'scope':'Controls of the all-apex algebraic identity; not a separator or matching theorem.'}
    (HERE/f'overnight_uniform_pruning_infinity_{mode}.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(rows),result['seconds'],flush=True)
if __name__=='__main__':main()
