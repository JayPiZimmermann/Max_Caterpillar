"""Exact separating input from the augmented braid-cone checker."""
from fractions import Fraction as Q
from pathlib import Path
import json
from overnight_fixed_physical_verify import check
from overnight_fixed_exact_counterexample import evaluate


def find(path):
    net=json.loads(Path(path).read_text());N=net['N']
    try:return None,check(path)
    except AssertionError as exc:failure=exc.args[0]
    assert isinstance(failure,tuple)and failure[0]in('UNCANCELLED_INTERIOR_WALL','WRONG_LINEAR_GRADIENT'),failure
    kind,p,data=failure;rays=[[Q(i in p[:t])-Q(N in p[:t])for i in range(N)]for t in range(1,N+1)]
    def point(gaps):return[sum(t*r[i]for t,r in zip(gaps,rays))for i in range(N)]
    def witness(x):
        actual=evaluate(net,x);target=max(x)
        if actual!=target:return{'point':list(map(str,x)),'network_value':str(actual),'target_value':str(target),'augmented_braid_cone':p,'source':kind}
    for gaps in [[Q(1)]*N]+[[Q(2 if i==j else 1)for i in range(N)]for j in range(N)]:
        w=witness(point(gaps))
        if w:return w,None
    if kind=='WRONG_LINEAR_GRADIENT':
        for r in rays:
            w=witness(r)
            if w:return w,None
    else:
        normal=next(g for g,c in data.items()if c);a=[sum(v*x for v,x in zip(normal,r))for r in rays];other=[[sum(v*x for v,x in zip(g,r))for r in rays]for g in data if g!=normal];neg=next(i for i,v in enumerate(a)if v<0);pos=next(i for i,v in enumerate(a)if v>0);gaps=None
        for integer in range(1,1000):
            t=[Q(integer**i)for i in range(N)];t[pos]+=1+sum((-v/a[pos])*(integer**i)for i,v in enumerate(a)if i!=neg and v<0);t[neg]=sum(v*t[i]for i,v in enumerate(a)if i!=neg)/(-a[neg]);assert all(v>0 for v in t)and sum(v*x for v,x in zip(a,t))==0
            if all(sum(v*x for v,x in zip(b,t))for b in other):gaps=t;break
        assert gaps is not None;eps=gaps[pos]/2
        for b in other:
            if b[pos]:eps=min(eps,abs(sum(v*x for v,x in zip(b,gaps)))/(2*abs(b[pos])))
        for sign in(-1,0,1):
            t=gaps[:];t[pos]+=sign*eps;w=witness(point(t))
            if w:return w,None
    raise AssertionError('uncancelled global defect gave no witness')
