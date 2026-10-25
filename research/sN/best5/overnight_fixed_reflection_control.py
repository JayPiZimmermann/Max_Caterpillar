"""Exact control of the involutive q3 folding and its generator formulas.

The finite ray gate proves the scalar folding globally. The uniform
no-relation theorem is proved symbolically in the accompanying note;
small matrix controls are not used as a substitute for that proof.
"""
import hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path


def norm(v):
    v=list(map(Q,v));den=math.lcm(*(c.denominator for c in v));w=[int(c*den)for c in v];g=math.gcd(*w)
    if not g:return None
    if next(c for c in w if c)<0:g=-g
    return tuple(c//g for c in w)


def S(x):return[2*sum(x)/3-c for c in x]
def q(x):return max(Q(0),min(x))
def g(x):
    sx=S(x);T=2*sum(x)/3;rang=sum(abs(x[i]-x[j])for i,j in itertools.combinations(range(3),2))/2
    return T-rang+sum(max(-c,Q(0))for c in x+sx)-sum(max(-v[i]-v[j],Q(0))for v in(x,sx)for i,j in itertools.combinations(range(3),2))


def matmul(A,B):return[[sum(a*b for a,b in zip(row,col))for col in zip(*B)]for row in A]


def main():
    start=time.monotonic();basis=[[Q(int(i==j))for i in range(3)]for j in range(3)];SR=[S(x)for x in basis];H={norm(x)for x in basis+SR}
    for i,j in itertools.combinations(range(3),2):
        H.add(norm([a-b for a,b in zip(basis[i],basis[j])]))
        for rows in(basis,SR):H.add(norm([a+b for a,b in zip(rows[i],rows[j])]))
    lines=set()
    for a,b in itertools.combinations(sorted(H),2):
        v=norm((a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]))
        if v:lines.add(v)
    for v in lines:
        for sign in(1,-1):
            x=[Q(sign*c)for c in v];assert S(S(x))==x;target=q(x)+q(S(x));value=g(x);assert max(value,Q(0))==target
            if not target:assert value<=0
    matrices=[]
    for N in(4,5,7,10):
        n=N-1;common=math.gcd(n,2);den=n//common;c=2//common;p=next(k for k in range(2,den+1)if den%k==0 and all(k%d for d in range(2,math.isqrt(k)+1)));R=[]
        for i in range(N):
            A=[[Q(int(j==i and k==i))if j==i or k==i else Q(2,n)-int(j==k)for k in range(N)]for j in range(N)];assert matmul(A,A)==[[Q(int(j==k))for k in range(N)]for j in range(N)];assert all(sum(row)==1 for row in A);assert all(sum(col)==1 for col in zip(*A));assert all(int(den*A[j][k])%p==(c*int(j!=i)*int(k!=i))%p for j in range(N)for k in range(N));R.append(A)
        assert all((N-2)%p!=0 for i,j in itertools.combinations(range(N),2));matrices.append({'N':N,'reduced_denominator':den,'prime':p,'generators':N,'status':'EXACT_GENERATOR_FORMULA_CONTROL_PASS'})
    report={'status':'EXACT_INVOLUTIVE_FOLDING_CONTROL_PASS','hyperplanes':len(H),'rays':2*len(lines),'identity':'sigma(g)=q+q_composed_with_S; S_squared=identity','matrix_controls':matrices,'scope':'The uniform reduced-word theorem is a written induction, not inferred from these controls.','seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_reflection_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True))

if __name__=='__main__':main()
