from pathlib import Path
from itertools import permutations
from emit_profile_targets import lookup
ROOT=Path(__file__).resolve().parents[4];OUT=ROOT/'MaxCaterpillar/Frontier/StarCertificate/XiPermutationGroups.lean'
P=list(permutations(range(5)));groups=[[j for j,p in enumerate(P) if sum(1<<i for i in p[:p.index(4)])==mask] for mask in range(16)]
assert sum(map(len,groups))==120
rows=['['+','.join(map(str,r))+']' for r in groups]
s='''import MaxCaterpillar.Frontier.StarCertificate.XiFastSelectors
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def permutationsBeforeMask (P : Fin 16) : List (Fin 120) :=
'''+lookup(rows,'P.val')+'''

theorem permutationsBeforeMask_nodup : ∀ P : Fin 16, (permutationsBeforeMask P).Nodup := by decide

theorem permutationsBeforeMask_toFinset : ∀ P : Fin 16,
    (permutationsBeforeMask P).toFinset =
      Finset.univ.filter (fun p => fastCenterBeforeMask p = P) := by decide

theorem sum_permutationsBeforeMask (P : Fin 16) (f : Fin 120 → ℤ) :
    ((permutationsBeforeMask P).map f).sum =
      ∑ p : Fin 120, if fastCenterBeforeMask p = P then f p else 0 := by
  rw [← List.sum_toFinset f (permutationsBeforeMask_nodup P),
    permutationsBeforeMask_toFinset, Finset.sum_filter]

end MaxCaterpillar.Frontier.StarCertificate
'''
q=OUT.with_suffix('.lean.tmp');q.write_text(s);q.replace(OUT)
