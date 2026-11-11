import MaxCaterpillar.Frontier.RandomRestriction.BraidModel
import MaxCaterpillar.Frontier.RandomRestriction.BraidModelRowInteraction
import MaxCaterpillar.Frontier.RandomRestriction.BraidModelRestriction

/-! # Exact actual quadratic interactions and original signed edge weights

This is coefficient equality, not a support overapproximation. Parallel
rows with opposite signed weights remain indexed and cancel on both sides.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open BigOperators NormalizedNetwork MaxCaterpillar.Frontier.StarCertificate
variable {h₁ h₂ N : ℕ}

theorem quadraticCombination_eq_braidEdgeWeight (A : Fin h₁→Point 5)
    (W : Fin h₁→ℝ) (pairs : ∀ j, BraidPair (A j))
    (a b : Fin 5) (hab : a≠b) :
    quadraticCombinationCoeff W A pairs a b+
      quadraticCombinationCoeff W A pairs b a=braidEdgeWeight A W a b := by
  classical
  have hsum : quadraticCombinationCoeff W A pairs a b+
      quadraticCombinationCoeff W A pairs b a=
      ∑ j, W j*((pairs j).quadraticCoeff a b+(pairs j).quadraticCoeff b a) := by
    unfold quadraticCombinationCoeff
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  unfold braidEdgeWeight braidEdgeRows
  rw [Finset.sum_filter,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(pairs j).quadraticCoeff_symm_eq_rowSupport a b hab]
  by_cases h : rowSupport (A j)={a,b} <;> simp [h]

/-- The constructed actual inner-neuron matrix has exactly the original
signed, parallel-row aggregate edge coefficient. -/
theorem inner_interaction_eq_braidEdgeWeight (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂)
    (a b : Fin 5) (hab : a≠b) :
    effectiveInteraction (innerQuadratic net pairs k) a b=
      braidEdgeWeight net.A (net.W k) a b :=
  quadraticCombination_eq_braidEdgeWeight net.A (net.W k) pairs a b hab

/-- Generic literal masked-restriction adapter. Actual localization supplies
the two displayed parameter equalities for each surviving outer index.
The conclusion retains the exact ambient cancellations defining its graph. -/
theorem inner_interaction_eq_ambient_of_masked_restrict
    (net : NormalizedNetwork 5 h₁ h₂) (pairs : ∀ j, BraidPair (net.A j))
    (k : Fin h₂) (e : Fin 5 ↪ Fin N)
    (A : Fin h₁→Point N) (W : Fin h₁→ℝ)
    (hA : ∀ j, net.A j=if rowSupport (A j)⊆Finset.univ.image e
      then restrict e (A j) else 0)
    (hW : ∀ j, rowSupport (A j)⊆Finset.univ.image e → net.W k j=W j)
    (a b : Fin 5) (hab : a≠b) :
    effectiveInteraction (innerQuadratic net pairs k) a b=
      braidEdgeWeight A W (e a) (e b) := by
  rw [inner_interaction_eq_braidEdgeWeight net pairs k a b hab]
  exact braidEdgeWeight_masked_restrict e A W net.A (net.W k) hA hW a b

#print axioms quadraticCombination_eq_braidEdgeWeight
#print axioms inner_interaction_eq_braidEdgeWeight
#print axioms inner_interaction_eq_ambient_of_masked_restrict
end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
