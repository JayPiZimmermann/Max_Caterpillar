"""EXACT check of k(3)=k(4)=1 claim (model A: Phi=(x_i, relu(x_i-x_j)), neurons relu(w.Phi))."""
import itertools, random
from fractions import Fraction as F
r=lambda t: max(t,0)
def m2(a,b): return b+r(a-b)
def up3(x): m=m2(x[1],x[2]); return m+r(x[0]-m)
def up4(x): a=m2(x[0],x[1]); b=m2(x[2],x[3]); return b+r(a-b)
random.seed(1)
for _ in range(20000):
    x=[F(random.randint(-50,50),random.randint(1,7)) for _ in range(4)]
    assert up3(x[:3])==max(x[:3]) and up4(x)==max(x)
def Lam(f,p,d):
    s=0
    for e in itertools.product((0,1),repeat=3):
        q=list(p)
        for t in range(3): q[t]+=d*e[t]
        s+=(-1)**(3-sum(e))*f(q)
    return s
d=F(1,10)
print('Lam max3 at 0:',Lam(max,[0,0,0],d),' Lam max4 at (0,0,0,-1):',Lam(max,[0,0,0,-1],d))
N=4;gens=[(lambda i:lambda x:x[i])(i) for i in range(N)]+[(lambda i,j:lambda x:r(x[i]-x[j]))(i,j) for i in range(N) for j in range(N) if i!=j]
for p in ([0,0,0,-1],[F(3,7),F(-2,5),F(1,3),F(5,2)]):
    assert all(Lam(g,p,d)==0 for g in gens)
print('Lambda kills all Phi generators: OK')
