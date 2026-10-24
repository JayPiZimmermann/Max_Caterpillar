from fractions import Fraction as F
import itertools, random
s=lambda t: t if t>0 else 0
def rhs(a,b,c,d,e):
    m=max
    mab,mac,mbc,mbd,mbe,mde=m(a,b),m(a,c),m(b,c),m(b,d),m(b,e),m(d,e)
    A=mde-mac; Q=F(1,2)*(mab+mbc-mbd-mbe)
    u=mbc+mbe-mab-mbd; v=mbc+mbd-mab-mbe
    return mab+s(A)-s(A+Q)+F(1,2)*s(u)+F(1,2)*s(v)
bad=0;n=0
R=range(-4,5)
for x in itertools.product(R,repeat=5):
    n+=1
    if rhs(*map(F,x))!=max(x): bad+=1; print(x)
random.seed(1)
for _ in range(200000):
    x=[F(random.randint(-10**6,10**6),random.randint(1,1000)) for _ in range(5)]
    n+=1
    if rhs(*x)!=max(x): bad+=1; print(x)
print(n,bad)
