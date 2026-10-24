# Exact check of k(3)=k(4)=1 claim: upper-bound identities on random rationals, and
# third mixed difference Lambda on Phi features and on max_N.
import itertools, random
from fractions import Fraction as F
s=lambda t: max(t,F(0))
def phi(x):
    N=len(x); return list(x)+[s(x[i]-x[j]) for i,j in itertools.combinations(range(N),2)]
random.seed(1)
for _ in range(20000):
    x=[F(random.randint(-50,50),random.randint(1,9)) for _ in range(4)]
    m12=x[2]+s(x[1]-x[2]); assert max(x[:3])==m12+s(x[0]-m12)
    m01=x[1]+s(x[0]-x[1]); m23=x[3]+s(x[2]-x[3]); assert max(x)==m23+s(m01-m23)
def Lam(f,base,d):
    tot=F(0)
    for e in itertools.product([0,1],repeat=3):
        y=list(base); 
        for k in range(3): y[k]+=d*e[k]
        tot+=(-1)**(3-sum(e))*f(y)
    return tot
for base in ([F(0)]*3,[F(0),F(0),F(0),F(-1)]):
    d=F(1,10)
    for t in range(len(phi(base))):
        assert Lam(lambda y:phi(y)[t],base,d)==0
    print(len(base),'Lambda max =',Lam(max,base,d))
# also random bases: Lambda kills Phi everywhere
for _ in range(2000):
    b=[F(random.randint(-20,20),7) for _ in range(4)]; d=F(random.randint(1,30),11)
    assert all(Lam(lambda y:phi(y)[t],b,d)==0 for t in range(10))
print('ok')
