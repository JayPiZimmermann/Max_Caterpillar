"""Exact S4 x global-sign orbit data for the resonance sign patterns."""
from itertools import permutations
from pathlib import Path
import json,hashlib
from emit_profile_targets import lookup,sign_vec
from certificate_arithmetic import vec
ROOT=Path(__file__).resolve().parents[4];D=Path(__file__).parent;BASE=ROOT/'MaxCaterpillar/Frontier/StarCertificate'
def write(p,s):
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists() and p.read_text()==s:return
 q=p.with_suffix('.lean.tmp');q.write_text(s);q.replace(p)
def main():
 raw=(D/'exact_tree_candidate.json').read_bytes();d=json.loads(raw);pats=[tuple(r['pattern']) for r in d['leaves']];ix={p:i for i,p in enumerate(pats)};perms=list(permutations(range(4)))
 maps=[[sum(1<<p[i] for i in range(4) if Q>>i&1) for Q in range(1,16)] for p in perms]
 reps=sorted({ix[min(tuple(ep*s[m-1] for m in mp) for mp in maps for ep in (-1,1))] for s in pats});rindex={j:i for i,j in enumerate(reps)};desc=[]
 for j,s in enumerate(pats):
  best=min(tuple(ep*s[m-1] for m in mp) for mp in maps for ep in (-1,1));rid=ix[best]
  found=next((p,negative) for negative in (False,True) for p,mp in enumerate(maps) if tuple((-1 if negative else 1)*s[m-1] for m in mp)==best)
  desc.append({'representative':rindex[rid],'representative_leaf':rid,'permutation':found[0],'negative':found[1]})
 assert len(reps)==67 and all(j<900 for j in reps)
 manifest={'input_sha256':hashlib.sha256(raw).hexdigest(),'permutations':perms,'mask_maps':maps,'representatives':reps,'descriptors':desc}
 (D/'orbit_manifest.json').write_text(json.dumps(manifest,separators=(',',':'))+'\n')
 s='''import MaxCaterpillar.Frontier.StarCertificate.XiEvenTargets
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators
'''
 s+='def leafPermutationTable : Fin 24 → Fin 4 → Fin 4 := '+vec([vec(list(map(str,p))) for p in perms])+'\n'
 s+='def leafMaskPermutation : Fin 24 → Fin 15 → Fin 15 := '+vec([vec([str(m-1) for m in mp]) for mp in maps])+'\n'
 s+='''
theorem leafPermutationTable_bijective : ∀ p : Fin 24, Function.Bijective (leafPermutationTable p) := by decide

noncomputable def leafPermutationEquiv (p : Fin 24) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (leafPermutationTable p) (leafPermutationTable_bijective p)

@[simp] theorem leafPermutationEquiv_apply (p : Fin 24) (i : Fin 4) :
    leafPermutationEquiv p i = leafPermutationTable p i := rfl

theorem subsetForms_leafPermutation : ∀ (p : Fin 24) (q : Fin 15) (i : Fin 4),
    subsetForms q i = subsetForms (leafMaskPermutation p q) (leafPermutationTable p i) := by decide

def reorderLeafPoint (p : Fin 24) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => z (leafPermutationTable p i)

theorem evalForm_reorderLeafPoint (p : Fin 24) (q : Fin 15) (z : Fin 4 → ℝ) :
    evalForm (subsetForms q) (reorderLeafPoint p z) =
      evalForm (subsetForms (leafMaskPermutation p q)) z := by
  unfold evalForm reorderLeafPoint
  apply Fintype.sum_equiv (leafPermutationEquiv p)
  intro i
  rw [leafPermutationEquiv_apply, ← subsetForms_leafPermutation p q i]

theorem actualSigns_reorderLeafPoint (p : Fin 24) (z : Fin 4 → ℝ) :
    actualSigns subsetForms (reorderLeafPoint p z) =
      fun q => actualSigns subsetForms z (leafMaskPermutation p q) := by
  funext q
  exact congrArg signOf (evalForm_reorderLeafPoint p q z)

structure OrbitDescriptor where
  representative : Fin 67
  permutation : Fin 24
  negative : Bool
  deriving DecidableEq, Repr

'''
 s+='def orbitRepresentativeLeaf : Fin 67 → Fin 900 := '+vec(list(map(str,reps)))+'\n'
 s+='def orbitRepresentativePattern (j : Fin 67) : Fin 15 → Sign :=\n'+lookup([sign_vec(pats[r]) for r in reps],'j.val')+'\n'
 s+='def orbitLeafPattern (j : Fin 900) : Fin 15 → Sign :=\n'+lookup([sign_vec(pats[j]) for j in range(900)],'j.val')+'\n'
 values=[f'⟨{r["representative"]},{r["permutation"]},{str(r["negative"]).lower()}⟩' for r in desc[:900]]
 s+='def orbitDescriptor (j : Fin 900) : OrbitDescriptor :=\n'+lookup(values,'j.val')+'\n'
 s+='''
def orbitPatternTransform (d : OrbitDescriptor) (s : Fin 15 → Sign) (q : Fin 15) : Sign :=
  let selected := s (leafMaskPermutation d.permutation q)
  if d.negative then selected.opposite else selected

def orbitPoint (d : OrbitDescriptor) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  if d.negative then fun i => -reorderLeafPoint d.permutation z i
  else reorderLeafPoint d.permutation z

theorem actualSigns_orbitPoint (d : OrbitDescriptor) (z : Fin 4 → ℝ) :
    actualSigns subsetForms (orbitPoint d z) = orbitPatternTransform d (actualSigns subsetForms z) := by
  unfold orbitPoint orbitPatternTransform
  split_ifs <;> simp only [actualSigns_neg, actualSigns_reorderLeafPoint]

end MaxCaterpillar.Frontier.StarCertificate
'''
 write(BASE/'XiOrbitData.lean',s)
 print('orbits',len(reps),'maxrep',max(reps),'source_bytes',len(s),flush=True)
if __name__=='__main__':main()
