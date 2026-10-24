# m=3, T=(x<a<w): search cubes with corner 0 and steps h=(hx,ha,hw) (rational) where
# Delta sigma(G)=0 but Delta max != 0. G = -2^x relu(zx-za) + 2^w relu(zw-za).
import itertools
from fractions import Fraction as F
relu=lambda v: max(v,0)
def Delta(f,h):
  s=0
  for e in itertools.product([0,1],repeat=3):
    z=[h[i]*e[i] for i in range(3)]; s+=(-1)**(3-sum(e))*f(z)
  return s
for (x,w) in [(0,2),(1,3),(0,5)]:
  G=lambda z: relu(-2**x*relu(z[0]-z[1])+2**w*relu(z[2]-z[1]))
  M=lambda z: max(z)
  vals=[F(k) for k in (-3,-2,-1,1,2,3)]
  hits=[h for h in itertools.product(vals,repeat=3) if Delta(G,h)==0 and Delta(M,h)!=0]
  print((x,w),len(hits),hits[:4])
