import research.sN.overnight_20261103.degree_two.ActualTie
import research.sN.overnight_20261103.degree_two.GraphBound
import research.sN.overnight_20261103.degree_two.CoverCounting
import research.sN.overnight_20261103.degree_two.ExponentialArithmetic

/-! An unconditional exponential second-hidden-width bound for actual braid
MAX networks whose signed interaction graphs have maximum degree two.
The first hidden width is unrestricted. Arbitrary real signed coefficients,
parallel-row cancellations, linear heads, and first-to-output skips are kept.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open Frontier Frontier.RandomRestriction NormalizedNetwork
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

/-- The exact binomial bound uses actual original neuron graphs. Every
selected set is covered by the proved local rank obstruction, and every
graph's capacity follows from maximum degree two. Neither is assumed. -/
theorem normalized_width_binomial [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x,net.eval x=Maximum N x)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,(braidInteractionGraph net hn k).degree v≤2)
    (m : ℕ) (hm : 3≤m) :
    N.choose m≤h₂*(2*N+2*(m-1)*N^2) := by
  have h := choose_le_card_mul_capacity
    (fun k => braidInteractionGraph net hn k) m (2*N+2*(m-1)*N^2) ?_ ?_
  · simpa only [Fintype.card_fin] using h
  · intro S hS
    obtain ⟨k,_hd,hk⟩ :=
      ExponentialPush.DegreeTwo.exists_active_second_on_set net hn hbraid hmax S
        (by simpa only [hS] using hm)
    exact ⟨k,hk⟩
  · intro k
    exact twoComponentSets_card_le (braidInteractionGraph net hn k)
      (hdegree k) m (lt_of_lt_of_le (by decide : 0<3) hm)

/-- A fully explicit exponential estimate, with no asymptotic notation.
The preceding binomial statement is sharper. -/
theorem normalized_width_exponential [NeZero N]
    (hN : 6≤N) (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (hmax : ∀ x,net.eval x=Maximum N x)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,(braidInteractionGraph net hn k).degree v≤2) :
    2^N≤h₂*(N^3*(N+1)) := by
  apply pow_two_le_width_polynomial N h₂ hN
  exact normalized_width_binomial net hn hmax hbraid hdegree (N/2)
    ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hN)

#check @normalized_width_binomial
#check @normalized_width_exponential
#print axioms normalized_width_binomial
#print axioms normalized_width_exponential
end MaxCaterpillar.Overnight.DegreeTwo
