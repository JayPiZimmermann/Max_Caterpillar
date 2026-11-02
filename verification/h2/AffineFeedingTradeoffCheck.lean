import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! Independent full affine-skip/original-feeding-width contract. -/
set_option autoImplicit false
noncomputable section
namespace AffineFeedingTradeoffCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction FeedingCore AffineSkipExtension
attribute [local instance] Classical.propDecidable

-- The denominator is exactly the ORIGINAL nonzero first-to-second columns,
-- before any normalization, support deletion or second-neuron freezing.
example {N h₁ h₂ : ℕ} (net : AffineSkipNetwork N h₁ h₂) :
    affineFeedingCard net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,net.W k j≠0} := by
  unfold affineFeedingCard
  exact Fintype.card_congr (Equiv.refl _)

-- Expanded nine-array/scalar formula, with every affine skip and bias present.
-- No first-width cap, normalized-model, certificate or probability assumption.
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k,d k*max 0 ((∑ j,W k j*max 0 ((∑ i,A j i*x i)+b j))+
        (∑ i,U k i*x i)+θ k))+
      ((∑ j,B j*max 0 ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2)
      ((N : ℝ)^4/(Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,W k j≠0} : ℝ))≤(h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  have hc : affineFeedingCard net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,W k j≠0} := by
    unfold affineFeedingCard
    exact Fintype.card_congr (Equiv.refl _)
  simpa only [hc] using affine_feeding_tradeoff hN net hmax

example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N)
    (net : AffineSkipNetwork N h₁ h₂) (hnet : ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hfeed : (Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,net.W k j≠0} : ℝ)≤(N : ℝ)^2) :
    (1/400000000 : ℝ)*(N : ℝ)^2≤(h₂ : ℝ) := by
  have hc : affineFeedingCard net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,net.W k j≠0} := by
    unfold affineFeedingCard
    exact Fintype.card_congr (Equiv.refl _)
  exact affine_feeding_quadratic hN net hnet (by simpa only [hc] using hfeed)

-- Half restriction keeps the original first AND second index types. All
-- three statistics refer to the same actual model and same selected set.
example {N n h₁ h₂ : ℕ} [NeZero N] [NeZero n] (hN : 5≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      4*ActualHalfRestriction.fourthMoment (core model)≤81*feedingCard net ∧
      4*ActualHalfRestriction.nonBraidCount (core model)≤feedingCard net ∧
      4*NetworkLowerBound.regularizedMoment (core model)≤81*feedingCard net :=
  exists_feeding_half_model hN net hn hnet hpair

-- Genuine boundary-arity witness for the stronger QUADRATIC feeding claim.
example : ∃ net : AffineSkipNetwork 1040 (firstWidth 1040) (secondWidth 1040),
    (∀ x,AffineSkipExtension.eval net x=Maximum 1040 x) ∧
    (affineFeedingCard net : ℝ)≤(1040 : ℝ)^2 ∧
    (1/400000000 : ℝ)*(1040 : ℝ)^2≤(secondWidth 1040 : ℝ) := by
  obtain ⟨net,hnet,_hbias,_hrational⟩ := caterpillar_net 1040
  have hm : ∀ x,AffineSkipExtension.eval (ofOrdinary net) x=Maximum 1040 x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hw : affineFeedingCard (ofOrdinary net)≤1040^2 :=
    (affineFeedingCard_le _).trans (by norm_num [firstWidth,Nat.choose_two_right])
  have hwr : (affineFeedingCard (ofOrdinary net) : ℝ)≤(1040 : ℝ)^2 := by exact_mod_cast hw
  exact ⟨ofOrdinary net,hm,hwr,affine_feeding_quadratic (by decide) _ hm hwr⟩

#check @affine_feeding_tradeoff
#check @affine_feeding_quadratic
#print axioms absorb_eval
#print axioms exists_original_matching_of_feeding_braid
#print axioms structural_witness_of_generic_embedding_feeding
#print axioms model_counting_feeding_on_tail
#print axioms feedingCard_pos
#print axioms exists_feeding_half_model
#print axioms normalized_feeding_tradeoff
#print axioms normalized_feedingCard_le_original
#print axioms affine_feeding_tradeoff
#print axioms affine_feeding_quadratic
end AffineFeedingTradeoffCheck
