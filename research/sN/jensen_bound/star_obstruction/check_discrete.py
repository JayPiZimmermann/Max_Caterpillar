"""Independent exact checker using signed-subset selectors, no face points.

Inputs only JSON candidate + tree artifact. Does not import either producer.
Checks tree coverage, all Farkas identities, solved multipliers, and that each
stored symbolic ANOVA target is obtained from Xi by sign-only selectors.
"""
from fractions import Fraction as Q
from itertools import permutations, combinations
from pathlib import Path
import json,time,hashlib
OUT=Path(__file__).parent

def signed_mask(mask):return [int(mask>>i&1) for i in range(4)]
def selected(T,chosen):
 leaves=sum(1<<i for i in chosen if i<4)
 return (-1,T&~leaves) if 4 in chosen else (1,T&leaves)
def sign_of(pattern,sel):
 s,m=sel;return s*pattern[m-1] if m else 0

def derive(pattern,coeffs,index):
 psi=[[[0]*4 for _ in range(16)] for _ in range(16)]
 for T in range(16):
  for p in permutations(range(5)):
   gamma=[selected(T,p[:r]) for r in range(1,5)]
   sg=[sign_of(pattern,e) for e in gamma]
   normal=next((s for s in sg if s),0)
   mixed=-1 in sg and 1 in sg
   if mixed:
    hs=[gamma[0],gamma[3]]+[selected(T,(p[i],p[j])) for i,j in combinations(range(5),2) if (i,j) not in [(0,2),(2,4)]]
    hpattern=tuple(normal*sign_of(pattern,e) for e in hs)
    k=coeffs[index[hpattern]]
   else:k=(10,-20,20,-10)
   P=sum(1<<i for i in p[:p.index(4)])
   for a,(s,m) in zip(k,gamma):
    for i in range(4):psi[T][P][i]+=a*normal*s*int(m>>i&1)
 C=[]
 for S in range(1,16):
  for A in range(16):
   if A&S!=A:continue
   row=[0]*4
   for T in range(16):
    if T&S!=T:continue
    sg=(-1)**((S^T).bit_count())
    for P in range(16):
     if P&S!=A:continue
     for i in range(4):row[i]+=sg*psi[T][P][i]
   C.append(row)
 return C

def main():
 start=time.time();d=json.load(open(OUT/'exact_tree_candidate.json'));c=json.load(open(OUT/'certificate_small_candidate.json'))
 assert d['candidate_sha256']==hashlib.sha256((OUT/'certificate_small_candidate.json').read_bytes()).hexdigest()
 coeffs=[[int(Q(x)*2) for x in c['coefficients'][j:j+4]] for j in range(0,900,4)]
 index={tuple(p):i for i,p in enumerate(c['patterns'])};seenL=set();seenE=set()
 def visit(t,prefix):
  kind=t[0]
  if kind=='branch':
   assert len(prefix)<15 and len(t)==4
   for s,child in zip((-1,0,1),t[1:]):visit(child,prefix+[s])
  elif kind=='exclude':
   idx=t[1];assert idx not in seenE;seenE.add(idx);e=d['excluded'][idx];assert e['prefix']==prefix
   w=list(map(Q,e['weights']));assert len(w)==len(prefix)
   assert all(s==0 or a>=0 for s,a in zip(prefix,w))
   assert sum(a for s,a in zip(prefix,w) if s)!=0
   for i in range(4):assert sum(a*(s or 1)*int((j+1)>>i&1) for j,(s,a) in enumerate(zip(prefix,w)))==0
  else:
   assert kind=='leaf' and len(prefix)==15
   idx=t[1];assert idx not in seenL;seenL.add(idx);l=d['leaves'][idx];assert l['pattern']==prefix
   assert l['identities']==derive(prefix,coeffs,index)
   for target,lam in zip(l['identities'],l['multipliers']):
    assert len(lam)==len(l['lambda_masks'])
    assert all(prefix[m-1]==0 for m in l['lambda_masks'])
    for i in range(4):assert sum(Q(a)*int(m>>i&1) for a,m in zip(lam,l['lambda_masks']))==target[i]
   if len(seenL)%200==0:print('independent leaves',len(seenL),'seconds',round(time.time()-start,1),flush=True)
 visit(d['tree'],[])
 assert len(seenL)==len(d['leaves']) and len(seenE)==len(d['excluded'])
 print('EXACT discrete checks passed:',len(seenL),'solved;',len(seenE),'impossible;',round(time.time()-start,1),'seconds',flush=True)
if __name__=='__main__':main()
