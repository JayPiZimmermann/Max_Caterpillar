import MaxCaterpillar.Frontier.RandomRestriction.FeedingHalf
import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization
import MaxCaterpillar.Frontier.SecondWidthPlus

/-! Final actual affine-skip tradeoff charged only to original feeding width. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
open BigOperators NormalizedNetwork NetworkLowerBound
variable {N n h₁ h₂ : ℕ}

theorem normalized_linear_bound [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hnet : ∀ x,net.eval x=Maximum N x) : N≤2*h₂+2 :=
  free_neurons h₁ h₂ net.L net.B net.A net.d net.U net.W (fun x => (hnet x).symm)

theorem model_counting_feeding [NeZero n]
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x) (hsize : 520≤n)
    (hbudget : 240*ActualHalfRestriction.nonBraidCount (core net)≤n.descFactorial 3) :
    NewCountingTradeoff.CountingPrerequisite 400 ((n : ℝ)-5)
      (regularizedMoment (core net) : ℝ) (h₂ : ℝ) := by
  obtain ⟨m,rfl⟩ : ∃ m,n=m+5 :=
    ⟨n-5,(Nat.sub_add_cancel ((by decide : 5≤520).trans hsize)).symm⟩
  have hm : 400≤m := by linarith only [hsize]
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_sub_cancel] using
    model_counting_feeding_on_tail net hn hnet hm hbudget

theorem normalized_feeding_tradeoff [NeZero N] (hN : 1040≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(feedingCard net : ℝ))≤(h₂ : ℝ) := by
  have hl := normalized_linear_bound net hnet
  have hlr : (N : ℝ)≤2*(h₂ : ℝ)+2 := by exact_mod_cast hl
  have hNr : (1040 : ℝ)≤(N : ℝ) := by exact_mod_cast hN
  have hW : (1 : ℝ)≤(h₂ : ℝ) := by linarith only [hlr,hNr]
  by_cases hwidth : 1000*(feedingCard net : ℝ)≤(N : ℝ)^3
  · letI : NeZero (N/2) := ⟨Nat.ne_of_gt
      (Nat.div_pos (le_trans (by decide : 2≤1040) hN) (by decide : 0<2))⟩
    obtain ⟨S,_hS,half,hmax,hnorm,_hmoment,hM,hreg⟩ :=
      exists_feeding_half_model (n := N/2) ((by decide : 5≤1040).trans hN) net hn hnet
        (by linarith only [Nat.mul_div_le N 2])
    have hc : 4*(ActualHalfRestriction.nonBraidCount (core half) : ℝ)≤(feedingCard net : ℝ) := by
      exact_mod_cast hM
    have hb := WeightedTradeoff.half_restriction_count_budget
      (N : ℝ) (N/2 : ℕ) (feedingCard net : ℝ)
      (ActualHalfRestriction.nonBraidCount (core half) : ℝ)
      (Nat.cast_nonneg _) (half_arity_ge_real hN) (half_arity_rounding_real N) hwidth hc
    rw [←descFactorial_three_real ((by decide : 2≤520).trans (half_arity_ge hN))] at hb
    have hbudget : 240*ActualHalfRestriction.nonBraidCount (core half)≤(N/2).descFactorial 3 := by
      exact_mod_cast hb
    have hcount := model_counting_feeding half hnorm hmax (half_arity_ge hN) hbudget
    apply NewCountingTradeoff.four_hundred_tradeoff (N : ℝ) (N/2 : ℕ)
      (feedingCard net : ℝ) (regularizedMoment (core half) : ℝ) (h₂ : ℝ)
      (Nat.cast_nonneg _) (half_arity_ge_real hN) (half_arity_three_real hN)
    · exact_mod_cast one_le_regularizedMoment (core half)
    · exact_mod_cast hreg
    · exact hW
    · exact hcount
  · exact NewCountingTradeoff.linear_absorption (N : ℝ) (feedingCard net : ℝ) (h₂ : ℝ)
      hNr (lt_of_not_ge hwidth) hlr

open AffineSkipExtension

noncomputable def affineFeedingCard (net : AffineSkipNetwork N h₁ h₂) : ℕ := by
  classical
  exact Fintype.card {j : Fin h₁ // ∃ k,net.W k j≠0}

theorem normalized_feedingCard_le_original (net : AffineSkipNetwork N h₁ h₂) :
    feedingCard (normalizedModel net)≤affineFeedingCard net := by
  classical
  apply Fintype.card_le_of_injective
    (fun j : {j : Fin h₁ // (normalizedModel net).Feeding j} =>
      (⟨j.val,normalizedModel_feeding_original net j.val j.property⟩ : {j : Fin h₁ // ∃ k,net.W k j≠0}))
  intro a b hab
  exact Subtype.ext (congrArg (fun q : {j : Fin h₁ // ∃ k,net.W k j≠0} => q.val) hab)

theorem affineFeedingCard_le (net : AffineSkipNetwork N h₁ h₂) : affineFeedingCard net≤h₁ := by
  classical
  exact (Fintype.card_subtype_le (fun j => ∃ k,net.W k j≠0)).trans_eq (Fintype.card_fin _)

theorem affineFeedingCard_pos [NeZero N] (hN : 5≤N)
    (net : AffineSkipNetwork N h₁ h₂) (hnet : ∀ x,AffineSkipExtension.eval net x=Maximum N x) :
    1≤affineFeedingCard net :=
  (feedingCard_pos hN (normalizedModel net) (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet)).trans (normalized_feedingCard_le_original net)

/-- Full Jensen-model scope, with original feeding width and arbitrary real
weights and all affine skips/biases. Every reduction and count is proved. -/
theorem affine_feeding_tradeoff (hN : 1040≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
      (1/400000000 : ℝ)*min ((N : ℝ)^2)
        ((N : ℝ)^4/(affineFeedingCard net : ℝ))≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet
  have hnorm := normalizedModel_translation_normalized net hnet
  have hmax := normalizedModel_computes_max net hnet
  have hbound := normalized_feeding_tradeoff hN (normalizedModel net) hnorm hmax
  have hp : (0 : ℝ)<(feedingCard (normalizedModel net) : ℝ) := by
    have hh := feedingCard_pos ((by decide : 5≤1040).trans hN) (normalizedModel net) hnorm hmax
    exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hh)
  have hc : (feedingCard (normalizedModel net) : ℝ)≤(affineFeedingCard net : ℝ) := by
    exact_mod_cast normalized_feedingCard_le_original net
  have hratio : (N : ℝ)^4/(affineFeedingCard net : ℝ)≤
      (N : ℝ)^4/(feedingCard (normalizedModel net) : ℝ) :=
    div_le_div_of_le_left (pow_nonneg (Nat.cast_nonneg N) 4) hp hc
  exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hratio) (by norm_num)).trans hbound

/-- A quadratic bound in the full affine-skip model, even when arbitrarily
many additional first neurons feed only the output. -/
theorem affine_feeding_quadratic (hN : 1040≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
      (affineFeedingCard net : ℝ)≤(N : ℝ)^2 →
      (1/400000000 : ℝ)*(N : ℝ)^2≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet hwidth
  have hp : (0 : ℝ)<(affineFeedingCard net : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0<1)
      (affineFeedingCard_pos ((by decide : 5≤1040).trans hN) net hnet)
  have hratio : (N : ℝ)^2≤(N : ℝ)^4/(affineFeedingCard net : ℝ) := by
    apply (le_div_iff hp).mpr
    calc
      (N : ℝ)^2*(affineFeedingCard net : ℝ)≤(N : ℝ)^2*(N : ℝ)^2 :=
        mul_le_mul_of_nonneg_left hwidth (sq_nonneg _)
      _ = (N : ℝ)^4 := by ring
  have hh := affine_feeding_tradeoff hN net hnet
  rwa [min_eq_left hratio] at hh

#print axioms exists_feeding_half_model
#print axioms normalized_feeding_tradeoff
#print axioms affine_feeding_tradeoff
#print axioms affine_feeding_quadratic
end MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
