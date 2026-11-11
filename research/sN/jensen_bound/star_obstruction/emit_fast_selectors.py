"""Emit balanced numeric selector lookups with checked canonical equalities."""
from pathlib import Path
from itertools import permutations,combinations
ROOT=Path(__file__).resolve().parents[4];OUT=ROOT/'MaxCaterpillar/Frontier/StarCertificate/XiFastSelectors.lean'
def vec(xs):return '!['+', '.join(xs)+']'
def pick(chosen):
 m=sum(1<<i for i in chosen if i<4);return (True,15&~m) if 4 in chosen else (False,m)
def lookup(rows,start=0,depth=1):
 pad='  '*depth
 if len(rows)==1:return pad+rows[0]
 k=len(rows)//2
 return pad+f'if p.val < {start+k} then (\n'+lookup(rows[:k],start,depth+1)+'\n'+pad+') else (\n'+lookup(rows[k:],start+k,depth+1)+'\n'+pad+')'
def main():
 P=list(permutations(range(5)));chain=[[pick(p[:r]) for r in range(1,5)] for p in P];coarse=[[g[0],g[3]]+[pick((p[i],p[j])) for i,j in combinations(range(5),2) if (i,j) not in [(0,2),(2,4)]] for p,g in zip(P,chain)]
 s='''import MaxCaterpillar.Frontier.StarCertificate.XiMasks
/-! Generated balanced arithmetic lookups. Closed finite proofs below connect
every entry to the canonical selector tables used by the real semantic proof. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate
'''
 for prefix,rows,n in [('Chain',chain,4),('Coarse',coarse,10)]:
  for field,typ,col in [('Mask','ℕ',1),('Negative','Bool',0)]:
   name='fast'+prefix+field;canonical=prefix.lower()+field
   values=[vec([('true' if x[col] else 'false') if typ=='Bool' else str(x[col]) for x in row]) for row in rows]
   s+=f'\ndef {name} (p : Fin 120) : Fin {n} → {typ} :=\n'+lookup(values)+'\n'
   s+=f'\ntheorem {name}_eq : ∀ (p : Fin 120) (j : Fin {n}), {name} p j = {canonical} p j := by decide\n'
 values=[str(sum(1<<i for i in p[:p.index(4)])) for p in P]
 s+='\ndef fastCenterBeforeMask (p : Fin 120) : Fin 16 :=\n'+lookup(values)+'\n'
 s+='''
theorem fastCenterBeforeMask_eq : ∀ p : Fin 120, fastCenterBeforeMask p = centerBeforeMask p := by decide

def fastMaskedChain (T : Fin 16) (p : Fin 120) (j : Fin 4) : FormRef 15 :=
  maskRef (fastChainNegative p j) (Nat.land T.val (fastChainMask p j))

def fastMaskedCoarse (T : Fin 16) (p : Fin 120) (j : Fin 10) : FormRef 15 :=
  maskRef (fastCoarseNegative p j) (Nat.land T.val (fastCoarseMask p j))

theorem fastMaskedChain_eq (T : Fin 16) (p : Fin 120) (j : Fin 4) :
    fastMaskedChain T p j = maskedChain T p j := by
  simp only [fastMaskedChain, maskedChain, fastChainNegative_eq, fastChainMask_eq]

theorem fastMaskedCoarse_eq (T : Fin 16) (p : Fin 120) (j : Fin 10) :
    fastMaskedCoarse T p j = maskedCoarse T p j := by
  simp only [fastMaskedCoarse, maskedCoarse, fastCoarseNegative_eq, fastCoarseMask_eq]

end MaxCaterpillar.Frontier.StarCertificate
'''
 q=OUT.with_suffix('.lean.tmp');q.write_text(s);q.replace(OUT)
if __name__=='__main__':main()
