import MaxCaterpillar.Frontier.StarCertificate.XiMasks
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate

/-- The first r+1 entries of the displayed chamber permutation. -/
def chamberPrefix (p : Fin 120) (r : Fin 4) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => ∃ k : Fin 5, k.val ≤ r.val ∧ permutationTable p k = i)

def starVCoefficient (p : Fin 120) (r i : Fin 4) : ℚ :=
  if (4 : Fin 5) ∈ chamberPrefix p r then 0
  else if i.castSucc ∈ chamberPrefix p r then 1 else 0

def starVPrimeCoefficient (p : Fin 120) (r i : Fin 4) : ℚ :=
  if (4 : Fin 5) ∈ chamberPrefix p r then
    if i.castSucc ∈ chamberPrefix p r then 0 else -1
  else 0

end MaxCaterpillar.Frontier.StarCertificate
