import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization

/-! # Conditional growing-matching lower bounds for raw affine-braid networks

Biases, skips and all real arrays are unrestricted. The original braid
condition is required only for zero-sum first covectors. Normalization and
the support bound on its actual first rows are derived, with no change to
the original two hidden-layer index types. The obstruction H(4q+1,q)
remains an explicit, unproved hypothesis at growing q.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineBraid
open BigOperators NormalizedNetwork AffineSkipExtension
variable {N h₁ h₂ : ℕ}

/-- A raw first layer is braid when each zero-sum covector is supported on
at most two input coordinates. Nonzero-sum covectors are unrestricted. -/
def BraidFirstLayer (net : AffineSkipNetwork N h₁ h₂) : Prop :=
  ∀ j,(∑ i,net.A j i)=0 → (rowSupport (net.A j)).card≤2

/-- The actual retained covectors inherit braid support from the original
raw arrays; this is a proved normalization bridge, not a model premise. -/
theorem normalizedModel_support_le_two (net : AffineSkipNetwork N h₁ h₂)
    (hbraid : BraidFirstLayer net) :
    ∀ j,(rowSupport ((normalizedModel net).A j)).card≤2 := by
  classical
  intro j
  rw [normalizedModel_first_row]
  split_ifs with h
  · exact hbraid j h.2
  · simp [rowSupport]

/-- A raw arbitrary-affine-skip MAX network with a braid first layer has
the finite exponential lower bound, conditional only on the explicitly
stated growing-order local matching obstruction. No normalization,
support-budget, scale, rank, or probability estimate is assumed. -/
theorem conditional_affine_braid_integer_q_lower_bound
    (q : ℕ) (hq : 1≤q) (hsize : 160000*q^2≤N)
    (H : LocalMatchingObstruction (Parameters.braidArity q) q)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := BraidCorollary.braidDimension_neZero N q hq hsize;
      ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hbraid : BraidFirstLayer net) :
    (23/25:ℝ)*4^q≤(h₂:ℝ) := by
  letI := BraidCorollary.braidDimension_neZero N q hq hsize
  exact BraidCorollary.conditional_braid_integer_q_lower_bound q hq hsize H
    (normalizedModel net) (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet) (normalizedModel_support_le_two net hbraid)

#check @conditional_affine_braid_integer_q_lower_bound
#print axioms normalizedModel_support_le_two
#print axioms conditional_affine_braid_integer_q_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineBraid
