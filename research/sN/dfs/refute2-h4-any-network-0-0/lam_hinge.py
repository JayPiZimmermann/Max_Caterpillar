# Exact corner-box k-th mixed difference (box [0,1]^k at the origin of the germ; delta=1 by homogeneity)
from itertools import product
from fractions import Fraction
s=lambda t: max(t,0)
def lam(F,k): return sum((-1)**(k-sum(e))*F(e) for e in product((0,1),repeat=k))
print("k=3 max:",lam(lambda e:max(e),3))
print("k=4 max:",lam(lambda e:max(e),4))
for a in [(1,1,-2),(1,2,-3),(2,-1,-1)]:
    print("k=3 hinge",a,lam(lambda e:s(sum(x*y for x,y in zip(a,e))),3))
for a in [(1,1,-1,-1),(1,-1,0,0),(3,1,-2,-2),(1,1,1,-3)]:
    print("k=4 hinge",a,lam(lambda e:s(sum(x*y for x,y in zip(a,e))),4))
