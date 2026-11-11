"""Exact candidate arithmetic and literal rendering for certificate emitters.

These routines propose finite data; the generated Lean proof independently
checks every used equality against the actual Xi coefficient definitions.
"""
from fractions import Fraction
from itertools import permutations, combinations

def vec(xs):return '!['+', '.join(xs)+']'
def tensor(x):
 if isinstance(x,list):return vec([tensor(y) for y in x])
 return str(int(x))
def psi_coefficients(pattern,c,only_T=None):
 ix={tuple(p):j for j,p in enumerate(c['patterns'])};K=[[int(Fraction(x)*2) for x in c['coefficients'][j:j+4]] for j in range(0,900,4)]
 def selected(T,chosen):
  leaves=sum(1<<i for i in chosen if i<4);return (-1,T&~leaves) if 4 in chosen else (1,T&leaves)
 def sign_of(sel):
  s,m=sel;return s*pattern[m-1] if m else 0
 out=[[[0]*4 for P in range(16)] for T in range(16)]
 for T in (range(16) if only_T is None else [only_T]):
  for p in permutations(range(5)):
   gamma=[selected(T,p[:r]) for r in range(1,5)];sg=[sign_of(x) for x in gamma];normal=next((s for s in sg if s),0)
   if -1 in sg and 1 in sg:
    hs=[gamma[0],gamma[3]]+[selected(T,(p[i],p[j])) for i,j in combinations(range(5),2) if (i,j) not in [(0,2),(2,4)]]
    k=K[ix[tuple(normal*sign_of(x) for x in hs)]]
   else:k=[10,-20,20,-10]
   P=sum(1<<i for i in p[:p.index(4)])
   for a,(s,m) in zip(k,gamma):
    for i in range(4):out[T][P][i]+=a*normal*s*int(m>>i&1)
 return out
