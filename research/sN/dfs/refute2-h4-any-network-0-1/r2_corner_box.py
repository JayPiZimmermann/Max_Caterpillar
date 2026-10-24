# Exact check: corner-box k-th mixed difference Lambda g = sum_S (-1)^{k-|S|} g(delta*1_S)
from fractions import Fraction as F
from itertools import combinations, product
relu=lambda x: x if x>0 else 0
def Lam(g,k,d=F(1)):
    return sum((-1)**(k-len(S))*g([d if i in S else 0 for i in range(k)])
               for r in range(k+1) for S in combinations(range(k),r))
# max_k
for k in (3,4,5): print("Lam max_%d ="%k, Lam(lambda z:max(z),k))
# k=3: all integer a with sum 0, |a_i|<=4 -> Lambda sigma(<a,z>) == 0 ?
bad3=[a for a in product(range(-4,5),repeat=3) if sum(a)==0 and Lam(lambda z:relu(sum(x*y for x,y in zip(a,z))),3)!=0]
print("k=3 sum-zero hinges with Lambda!=0:",len(bad3))
# k=4: counterexample
a=(1,2,-1,-2)
print("k=4 a=",a,"Lambda sigma(<a,z>) =",Lam(lambda z:relu(sum(x*y for x,y in zip(a,z))),4))
cnt=[a for a in product(range(-3,4),repeat=4) if sum(a)==0 and all(a) and Lam(lambda z:relu(sum(x*y for x,y in zip(a,z))),4)!=0]
print("k=4 full-support sum-zero hinges (|a_i|<=3) with Lambda!=0:",len(cnt), cnt[:5])
