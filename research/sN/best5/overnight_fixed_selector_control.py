"""Exact global scalar-identity controls; standard library only.

A recursive gradient overapproximation includes every possible branch wall.
Coordinate walls make each arrangement cone pointed. Every extreme ray is
an intersection of d-1 independent walls, so equality at all enumerated
rays proves the homogeneous identity on every cone, hence globally.
"""
import hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path


def canonical(v):
    den=math.lcm(*(Q(c).denominator for c in v));w=[int(Q(c)*den)for c in v];g=math.gcd(*w)
    if not g:return None
    if next(c for c in w if c)<0:g=-g
    return tuple(c//g for c in w)

class E:
    def __init__(self,kind,children=(),vector=None,coefficient=None):self.kind=kind;self.children=children;self.vector=vector;self.coefficient=coefficient;self.cached=None
    def __add__(self,other):return E('add',(self,other))
    def __neg__(self):return E('scale',(self,),coefficient=-1)
    def __sub__(self,other):return self+-other
    def __mul__(self,c):return E('scale',(self,),coefficient=Q(c))
    def value(self,x):
        if self.kind=='linear':return sum(Q(a)*b for a,b in zip(self.vector,x))
        a=self.children[0].value(x)
        if self.kind=='scale':return self.coefficient*a
        b=self.children[1].value(x)
        return a+b if self.kind=='add'else max(a,b)if self.kind=='max'else min(a,b)
    def gradients(self):
        if self.cached is not None:return self.cached
        if self.kind=='linear':result=({tuple(map(Q,self.vector))},set())
        else:
            A,HA=self.children[0].gradients()
            if self.kind=='scale':result=({tuple(self.coefficient*c for c in a)for a in A},HA)
            else:
                B,HB=self.children[1].gradients();H=HA|HB
                if self.kind=='add':G={tuple(a+b for a,b in zip(x,y))for x in A for y in B}
                else:
                    G=A|B;H=H|{v for x in A for y in B if(v:=canonical(tuple(a-b for a,b in zip(x,y))))is not None}
                result=(G,H)
        self.cached=result;return result


def maximum(*xs):
    a=xs[0]
    for b in xs[1:]:a=E('max',(a,b))
    return a

def minimum(a,b):return E('min',(a,b))
def sigma(a,zero):return maximum(a,zero)

def ray(rows,d):
    M=[list(map(Q,r))for r in rows];piv=[];at=0
    for c in range(d):
        p=next((r for r in range(at,len(M))if M[r][c]),None)
        if p is None:continue
        M[p],M[at]=M[at],M[p];v=M[at][c];M[at]=[x/v for x in M[at]]
        for r in range(len(M)):
            if r!=at:
                t=M[r][c];M[r]=[x-t*y for x,y in zip(M[r],M[at])]
        piv.append(c);at+=1
    if len(piv)!=d-1:return None
    free=next(c for c in range(d)if c not in piv);v=[Q(0)]*d;v[free]=1
    for r,c in zip(M,piv):v[c]=-r[free]
    return canonical(v)


def verify(name,left,right,d):
    H=left.gradients()[1]|right.gradients()[1]|{tuple(int(i==j)for i in range(d))for j in range(d)};lines=set()
    for selected in itertools.combinations(sorted(H),d-1):
        v=ray(selected,d)
        if v:lines.add(v)
    for v in lines:
        for s in(1,-1):
            x=[Q(s*c)for c in v];assert left.value(x)==right.value(x),(name,x,left.value(x),right.value(x))
    result={'identity':name,'dimension':d,'arrangement_hyperplanes':len(H),'arrangement_rays':2*len(lines),'status':'EXACT_GLOBAL_IDENTITY_PASS'};print(json.dumps(result),flush=True);return result


def variables(d):return [E('linear',vector=tuple(int(i==j)for i in range(d)))for j in range(d)],E('linear',vector=(0,)*d)

def selector(a,b,c,s,z):
    A=a-maximum(b,c);B=b-maximum(a,c);C=c-maximum(a,b);R=maximum(a,c)+maximum(b,c)-maximum(a,b)-s
    return R+sigma(A+s,z)+sigma(B+s,z)-sigma(C-s,z)


def main():
    start=time.monotonic();records=[];(b,c,h),a=variables(3);records.append(verify('four_scalar_selector',selector(a,b,c,sigma(h,a),a),maximum(a,b,c,minimum(a,b)+h),3));(b,c,d,e),a=variables(4);m=minimum(a,b);M=maximum(a,b);D=maximum(d,e);h=D-m;target=maximum(a,b,c,d,e);error=minimum(sigma(m*2-M-D,a),sigma(m-c,a));records.append(verify('naive_five_input_exact_error',selector(a,b,c,h,a),target+error,4));G1=a-maximum(b,c)+D-m;G2=b-maximum(a,c)+D-m;G3=maximum(c,m)-M-D+m;R=maximum(a,c)+maximum(b,c)-M-D+m;records.append(verify('corrected_three_outer_identity',R+sigma(G1,a)+sigma(G2,a)-sigma(G3,a),target,4));records.append(verify('negative_preactivation_is_negative_maximum',G3,-maximum(G1,G2),4));(g,s),z=variables(2);absolute=lambda v:maximum(v,-v);records.append(verify('symmetric_three_way_split',sigma(g+s,z)+sigma(g-s,z)-sigma(g,z),sigma(g,z)+sigma(absolute(s)-absolute(g),z),2))
    # Exact normal jumps at two open positive patches of the bad preactivation.
    def G(w,c0):
        aa=w/2;bb=-w/2;mm=min(aa,bb);MM=max(aa,bb);return max(c0,mm)-MM+1+mm
    eps=Q(1,10);jumps=[]
    for c0 in(Q(-2),Q(2)):
        value=G(Q(0),c0);assert value>0 and G(eps,c0)>0 and G(-eps,c0)>0;jump=(G(eps,c0)-value)/eps-(value-G(-eps,c0))/eps;jumps.append(str(jump))
    assert jumps==['-3','-2'];report={'status':'EXACT_SELECTOR_IDENTITY_CONTROLS_PASS','identities':records,'normal_jump_controls':jumps,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Global finite ray certificates for the displayed identities; not a proof of the unrestricted width bound'};Path('overnight_fixed_selector_control.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
