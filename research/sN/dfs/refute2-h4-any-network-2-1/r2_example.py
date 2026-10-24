"""Counterexample to 'Lambda=0 when c not in T': N=5, c=4, T={0,1,2,3}, s=(1,1,-1,-1).
At p_L (x_T=0, x_4=-B), g(p)=B*(1+1-1-1)=0 and the germ is sigma(z0+z1-z2-z3)."""
from fractions import Fraction as Fr
from itertools import combinations
relu=lambda t: t if t>0 else 0
s={0:1,1:1,2:-1,3:-1}; c=4; B=Fr(10**4); dl=Fr(1,10**6)
g=lambda x: sum(so*relu(x[o]-x[c]) for o,so in s.items())
T=(0,1,2,3); tot=Fr(0)
for r in range(5):
    for S in combinations(T,r):
        x=[Fr(0)]*4+[-B]
        for t in S: x[t]+=dl
        tot+=(-1)**(4-r)*relu(g(x))
print("Lambda/delta =", tot/dl)
