"""Produce a rational input witness from a failed exact braid-cone check."""
from fractions import Fraction as Q
from pathlib import Path
import json
from overnight_fixed_anchor_verify import check


def evaluate(net,x):
    first=[max(sum(Q(v)*t for v,t in zip(row,x)),Q(0))for row in net['first_layer']];second=[max(sum(Q(v)*t for v,t in zip(row,first)),Q(0))for row in net['second_layer']];return sum(Q(v)*t for v,t in zip(net['output'],second))


def find(path):
    net=json.loads(Path(path).read_text());N=net['N']
    try:receipt=check(path);return None,receipt
    except AssertionError as exc:failure=exc.args[0]
    assert isinstance(failure,tuple)and failure[0]in('UNCANCELLED_INTERIOR_WALL','WRONG_LINEAR_GRADIENT'),failure
    kind,perm,data=failure
    def point(gaps):return[sum(gaps[k]for k in range(N-1)if i in perm[:k+1])for i in range(N)]
    # Prefer a small exact witness in the failing cone; this is only witness
    # simplification. The isolated-wall construction below is the fallback.
    for gaps in [[Q(1)]*(N-1)]+[[Q(2 if i==j else 1)for i in range(N-1)]for j in range(N-1)]:
        x=point(gaps);value=evaluate(net,x);target=max(x)
        if value!=target:return {'point':list(map(str,x)),'network_value':str(value),'target_value':str(target),'source':'EXACT_INTEGER_POINT_IN_FAILING_CONE','braid_cone':perm},None
    trials=[]
    if kind=='WRONG_LINEAR_GRADIENT':
        for k in range(1,N):trials.append([Q(i in perm[:k])for i in range(N)])
    else:
        normal=next(g for g,c in data.items()if c);a=[sum(normal[perm[j]]for j in range(k))for k in range(1,N)];assert min(a)<0<max(a);other=[[sum(g[perm[j]]for j in range(k))for k in range(1,N)]for g in data if g!=normal];neg=next(j for j,v in enumerate(a)if v<0);pos=next(j for j,v in enumerate(a)if v>0);gaps=None
        for integer in range(1,1000):
            t=[Q(integer**i)for i in range(N-1)];t[pos]+=1+sum((-v/a[pos])*(integer**i)for i,v in enumerate(a)if i!=neg and v<0);t[neg]=sum(v*t[i]for i,v in enumerate(a)if i!=neg)/(-a[neg]);assert all(v>0 for v in t)and sum(v*x for v,x in zip(a,t))==0
            if all(sum(v*x for v,x in zip(b,t))for b in other):gaps=t;break
        assert gaps is not None;eps=gaps[pos]/2
        for b in other:
            if b[pos]:eps=min(eps,abs(sum(v*x for v,x in zip(b,gaps)))/(2*abs(b[pos])))
        assert eps>0
        for sign in(-1,0,1):
            t=gaps[:];t[pos]+=sign*eps;assert all(v>0 for v in t);trials.append(point(t))
    for x in trials:
        value=evaluate(net,x);target=max(x)
        if value!=target:return{'point':list(map(str,x)),'network_value':str(value),'target_value':str(target),'source':kind,'braid_cone':perm},None
    raise AssertionError('failed wall produced no exact counterexample')


if __name__=='__main__':
    import sys
    counter,receipt=find(sys.argv[1]);print(json.dumps({'counterexample':counter,'global_check':receipt},sort_keys=True))
