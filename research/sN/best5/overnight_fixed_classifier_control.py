"""Exact whole-domain control of the shallow three-comparison classifier.

The13 hyperplanes contain every first-layer wall and every branch wall
of q and q composed with A. Coordinate walls make each cone pointed.
The checked signs make sigma(g) linear on every arrangement cone as well.
"""
import hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path


def norm(v):
    d=math.gcd(*v)
    if not d:return None
    if next(c for c in v if c)<0:d=-d
    return tuple(c//d for c in v)


def g(x):
    a,b,c=x;F=2*sum(abs(x[i]+x[j])-abs(x[i]-x[j])for i,j in itertools.combinations(range(3),2))-3*abs(a+b+c)+abs(a+b-c)+abs(a-b+c)+abs(-a+b+c)
    return a+b+c-sum(map(abs,x))+F/Q(4)


def main():
    start=time.monotonic();H=set()
    for i in range(3):H.add(tuple(int(i==j)for j in range(3)))
    for i,j in itertools.combinations(range(3),2):
        for s in(1,-1):v=[0]*3;v[i]=1;v[j]=s;H.add(norm(v))
    H.update(norm(v)for v in((1,1,1),(1,1,-1),(1,-1,1),(-1,1,1)));lines=set()
    for a,b in itertools.combinations(sorted(H),2):
        v=norm((a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]))
        if v:lines.add(v)
    for v in lines:
        for sign in(1,-1):
            x=[Q(sign*c)for c in v];value=g(x)
            if min(x)>=0:assert value>=0
            else:assert value<=0
            if min(x)==0 and min(x)>=0:assert value==0
            Ax=[sum(x)-2*c for c in x];q=max(Q(0),min(x));qa=max(Q(0),min(Ax));assert max(value,Q(0))==q+qa/2
    r={'status':'EXACT_GLOBAL_SHALLOW_CLASSIFIER_IDENTITY_PASS','hyperplanes':len(H),'rays':2*len(lines),'identity':'sigma(g)=positive_minimum3+(1/2)positive_minimum3_composed_with_A','seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_classifier_check.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r,sort_keys=True))

if __name__=='__main__':main()
