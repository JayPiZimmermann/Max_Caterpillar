import research.sN.overnight_20261103.portfolio.coordinate_quotient.Model
import research.sN.overnight_20261103.portfolio.transversal.Bounds

/-! Existing braid bounds transported through the exact coordinate quotient.
No first-width restriction is imposed. These corollaries do not improve the
optimal retained-coordinate criterion; see Section.lean. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.CoordinateQuotient
open BigOperators Frontier Frontier.RandomRestriction AffineSkipExtension GrowingMatching
variable {N m h₁ h₂ : ℕ}

theorem affine_quotient_quadratic [NeZero N] [NeZero m] (hm : 3 ≤ m)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, eval net x = Maximum N x)
    (φ : Fin N → Fin m) (hφ : Function.Surjective φ)
    (hbraid : BraidBlockSums net φ) :
    (m:ℝ)^2 / 3000000 ≤ (h₂:ℝ) := by
  obtain ⟨model, hmax, hnorm, hb⟩ :=
    exists_normalized_braid_quotient net hnet φ hφ hbraid
  exact SupportTransversal.normalized_braid_quadratic hm model hnorm hmax hb

theorem conditional_affine_quotient_lower_bound [NeZero N]
    (q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ m)
    (H : LocalMatchingObstruction (Parameters.braidArity q) q)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, eval net x = Maximum N x)
    (φ : Fin N → Fin m) (hφ : Function.Surjective φ)
    (hbraid : BraidBlockSums net φ) :
    (23/25:ℝ)*4^q ≤ (h₂:ℝ) := by
  letI : NeZero m := BraidCorollary.braidDimension_neZero m q hq hsize
  obtain ⟨model, hmax, hnorm, hb⟩ :=
    exists_normalized_braid_quotient net hnet φ hφ hbraid
  exact BraidCorollary.conditional_braid_integer_q_lower_bound
    q hq hsize H model hnorm hmax hb

#check @affine_quotient_quadratic
#check @conditional_affine_quotient_lower_bound
#print axioms affine_quotient_quadratic
#print axioms conditional_affine_quotient_lower_bound
end MaxCaterpillar.Overnight.CoordinateQuotient
