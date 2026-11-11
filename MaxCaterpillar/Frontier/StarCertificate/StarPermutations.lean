import MaxCaterpillar.Frontier.StarCertificate.StarModel
import MaxCaterpillar.Frontier.StarCertificate.XiPermutations

/-! # Reindexing actual star chains over all permutations -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def permutationPrefix (e : Equiv.Perm (Fin 5)) (r : Fin 4) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => ∃ k : Fin 5, k.val ≤ r.val ∧ e k = i)

noncomputable def permutationFunctionChain (G : Finset (Fin 5) → ℝ)
    (e : Equiv.Perm (Fin 5)) : Fin 4 → ℝ :=
  fun r => G (permutationPrefix e r)

theorem permutationFunctionChain_star_table (v v' : Fin 4 → ℝ) (p : Fin 120) :
    permutationFunctionChain (starSetFunction v v') (permutationEquiv p) = starChain v v' p := rfl

theorem sum_starXi_permutations (v v' : Fin 4 → ℝ) :
    (∑ e : Equiv.Perm (Fin 5), starXi (permutationFunctionChain (starSetFunction v v') e)) =
      ∑ p : Fin 120, starXi (starChain v v' p) := by
  rw [← sum_permutationTable]
  simp only [permutationFunctionChain_star_table]

/-- The all-permutations statement for actual star set functions follows
from the concrete coefficient certificate, once that finite check is attached. -/
theorem star_permutation_sum_of_coefficients
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0)
    (v v' : Fin 4 → ℝ) :
    (∑ e : Equiv.Perm (Fin 5), starXi (permutationFunctionChain (starSetFunction v v') e)) = 0 := by
  rw [sum_starXi_permutations]
  exact star_sum_of_coefficients hcoeff v v'

end MaxCaterpillar.Frontier.StarCertificate
