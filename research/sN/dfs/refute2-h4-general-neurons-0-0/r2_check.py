from fractions import Fraction as F
import itertools, random
s=lambda t: t if t>0 else 0
def rhs(a,b,c,d,e):
    m=lambda x,y: max(x,y)
    A=m(d,e)-m(a,c); Q=F(1,2)*(m(a,b)+m(b,c)-m(b,d)-m(b,e))
    u=m(b,c)+m(b,e)-m(a,b)-m(b,d); v=m(b,c)+m(b,d)-m(a,b)-m(b,e)
    return m(a,b)+s(A)-s(A+Q)+F(1,2)*s(u)+F(1,2)*s(v)
bad=0;n=0
for p in itertools.product(range(-3,4),repeat=5):
    n+=1
    if rhs(*map(F,p))!=max(p): bad+=1
random.seed(1)
for _ in range(200000):
    p=[F(random.randint(-50,50),random.randint(1,7)) for _ in range(5)]
    n+=1
    if rhs(*p)!=max(p): bad+=1;print(p)
print(n,bad)
