import research.sN.overnight_20261103.degree_two.RawBound
import research.sN.overnight_20261103.degree_two.ActualTieFeeding
import research.sN.overnight_20261103.degree_two.GraphSharpCover
import research.sN.overnight_20261103.degree_two.GraphSharpArithmetic

/-! The sharp connected-set capacity removes the coarse factor four.
The normalized version also only requires braid rows where they feed a
second-hidden neuron; output-only rows may have arbitrary support. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open AffineSkipExtension
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

theorem normalized_width_binomial_sharp_feeding [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x,net.eval x=Maximum N x)
    (hbraid : ∀ k j,net.W k j≠0 → (rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,(braidInteractionGraph net hn k).degree v≤2)
    (m : ℕ) (hm : 3≤m) :
    2*N.choose m≤h₂*(2*N+(m-1)*N^2) := by
  have h := two_choose_le_card_mul_sharp_capacity
    (fun k => braidInteractionGraph net hn k) hdegree m
    (lt_of_lt_of_le (by decide : 0<3) hm) ?_
  · simpa only [Fintype.card_fin] using h
  · intro S hS
    obtain ⟨k,_hd,hk⟩ :=
      ExponentialPush.DegreeTwo.exists_active_second_on_set_feeding net hn hbraid hmax S
        (by simpa only [hS] using hm)
    exact ⟨k,hk⟩

theorem raw_width_binomial_sharp [NeZero N]
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hA : ∀ j,∑ i,net.A j i=0)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,
      (ExponentialPush.DegreeTwo.Recession.rawInteractionGraph net hA k).degree v≤2)
    (m : ℕ) (hm : 3≤m) :
    2*N.choose m≤h₂*(2*N+(m-1)*N^2) := by
  let model := ExponentialPush.DegreeTwo.Recession.normalized net
  have hn : model.TranslationNormalized :=
    ExponentialPush.DegreeTwo.Recession.normalized_translation net hA hmax
  apply normalized_width_binomial_sharp_feeding model hn
    (ExponentialPush.DegreeTwo.Recession.normalized_computes_max net hA hmax)
    (fun _ j _ => hbraid j) ?_ m hm
  intro k v
  exact (ExponentialPush.DegreeTwo.Recession.normalized_degree_le_raw net hA hn k v).trans
    (hdegree k v)

theorem raw_width_exponential_sharp [NeZero N]
    (hN : 6≤N) (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hA : ∀ j,∑ i,net.A j i=0)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,
      (ExponentialPush.DegreeTwo.Recession.rawInteractionGraph net hA k).degree v≤2) :
    4*2^N≤h₂*(N^3*(N+1)) := by
  apply four_pow_two_le_width_polynomial N h₂ (le_trans (by decide : 2≤6) hN)
  exact raw_width_binomial_sharp net hmax hA hbraid hdegree (N/2)
    ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hN)

theorem raw_width_exponential_sharp_real [NeZero N]
    (hN : 6≤N) (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hA : ∀ j,∑ i,net.A j i=0)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hdegree : ∀ k v,
      (ExponentialPush.DegreeTwo.Recession.rawInteractionGraph net hA k).degree v≤2) :
    (4:ℝ)*2^N/((N:ℝ)^3*((N:ℝ)+1))≤(h₂:ℝ) := by
  have hNp : (0:ℝ)<N := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0<6) hN)
  have hd : (0:ℝ)<(N:ℝ)^3*((N:ℝ)+1) :=
    mul_pos (pow_pos hNp 3) (by linarith only [hNp])
  apply (div_le_iff hd).mpr
  exact_mod_cast raw_width_exponential_sharp hN net hmax hA hbraid hdegree

#check @normalized_width_binomial_sharp_feeding
#check @raw_width_binomial_sharp
#check @raw_width_exponential_sharp_real
#print axioms normalized_width_binomial_sharp_feeding
#print axioms raw_width_binomial_sharp
#print axioms raw_width_exponential_sharp
#print axioms raw_width_exponential_sharp_real
end MaxCaterpillar.Overnight.DegreeTwo
