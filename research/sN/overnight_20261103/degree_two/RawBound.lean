import research.sN.overnight_20261103.degree_two.NormalizedBound
import research.sN.overnight_20261103.degree_two.RecessionGraph

/-! The degree-two exponential estimate for the original nine real arrays.
First and second biases, linear heads, first-hidden output skips, and all
coefficient signs are unrestricted. Every first covector is a scalar input
difference (or zero), and each ORIGINAL signed interaction graph has degree
at most two. No cap on the first hidden width occurs. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open AffineSkipExtension
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

/-- The raw nine-array binomial bound. Bias removal retains every original
first covector and weight, so cancellation in the original interaction graph
cannot be unmasked by deleting biased rows. -/
theorem raw_width_binomial [NeZero N]
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hA : ∀ j,∑ i,net.A j i=0)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,
      (ExponentialPush.DegreeTwo.Recession.rawInteractionGraph net hA k).degree v≤2)
    (m : ℕ) (hm : 3≤m) :
    N.choose m≤h₂*(2*N+2*(m-1)*N^2) := by
  let model := ExponentialPush.DegreeTwo.Recession.normalized net
  have hn : model.TranslationNormalized :=
    ExponentialPush.DegreeTwo.Recession.normalized_translation net hA hmax
  apply normalized_width_binomial model hn
    (ExponentialPush.DegreeTwo.Recession.normalized_computes_max net hA hmax)
    hbraid ?_ m hm
  intro k v
  exact (ExponentialPush.DegreeTwo.Recession.normalized_degree_le_raw net hA hn k v).trans
    (hdegree k v)

/-- A literal exponential lower bound on the original second-hidden width,
valid with arbitrary first-hidden width and arbitrary real biases and skips. -/
theorem raw_width_exponential [NeZero N]
    (hN : 6≤N) (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hA : ∀ j,∑ i,net.A j i=0)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,
      (ExponentialPush.DegreeTwo.Recession.rawInteractionGraph net hA k).degree v≤2) :
    2^N≤h₂*(N^3*(N+1)) := by
  apply pow_two_le_width_polynomial N h₂ hN
  exact raw_width_binomial net hmax hA hbraid hdegree (N/2)
    ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hN)

/-- The same estimate in the customary lower-bound format. -/
theorem raw_width_exponential_real [NeZero N]
    (hN : 6≤N) (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hA : ∀ j,∑ i,net.A j i=0)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,
      (ExponentialPush.DegreeTwo.Recession.rawInteractionGraph net hA k).degree v≤2) :
    (2:ℝ)^N/((N:ℝ)^3*((N:ℝ)+1))≤(h₂:ℝ) := by
  have hNp : (0:ℝ)<N := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0<6) hN)
  have hd : (0:ℝ)<(N:ℝ)^3*((N:ℝ)+1) :=
    mul_pos (pow_pos hNp 3) (by linarith only [hNp])
  apply (div_le_iff hd).mpr
  exact_mod_cast raw_width_exponential hN net hmax hA hbraid hdegree

#check @raw_width_binomial
#check @raw_width_exponential
#check @raw_width_exponential_real
#print axioms raw_width_binomial
#print axioms raw_width_exponential
#print axioms raw_width_exponential_real
end MaxCaterpillar.Overnight.DegreeTwo
