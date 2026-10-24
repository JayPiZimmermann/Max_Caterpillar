# EXACT (Fractions): k-th mixed difference at a corner box of side d, base point arbitrary b.
# Checks (1) odd k: every sum-zero hinge supported in T is killed (pairing S<->S^c proof);
# (2) even k: sum-zero full-support hinges are NOT killed, for several base offsets.
from fractions import Fraction as F
from itertools import combinations, product
relu=lambda x: x if x>0 else 0
def Lam(g,k,d,b):
    return sum((-1)**(k-len(S))*g([b[i]+(d if i in S else 0) for i in range(k)])
               for r in range(k+1) for S in combinations(range(k),r))
hinge=lambda a:(lambda z:relu(sum(x*y for x,y in zip(a,z))))
for k in (3,4,5,6):
    d=F(1,7); b=[F(0)]*k
    print("k",k,"Lam max =",Lam(lambda z:max(z),k,d,b)/d)
    R=range(-2,3)
    vs=[a for a in product(R,repeat=k) if sum(a)==0 and any(a)]
    bad=[a for a in vs if Lam(hinge(a),k,d,b)!=0]
    print("  sum-zero hinges |a_i|<=2:",len(vs),"with Lam!=0:",len(bad), bad[:3])
# the even-k witness and its value
a=(1,2,-1,-2); print("Lam sigma(z1+2z2-z3-2z4)/d =",Lam(hinge(a),4,F(1,7),[0]*4)/F(1,7))
