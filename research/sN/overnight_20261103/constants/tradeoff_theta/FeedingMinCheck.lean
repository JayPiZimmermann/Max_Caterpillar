import research.sN.overnight_20261103.constants.tradeoff_theta.FeedingMin

/-! Independent literal-original-column contract for the improved feeding tradeoff. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta.Feeding.Check
open BigOperators Frontier Frontier.RandomRestriction AffineSkipExtension FeedingCore
attribute [local instance] Classical.propDecidable

theorem exact_raw_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 3≤N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x) :
    min ((N:ℝ)^2)
      ((N:ℝ)^4/(Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, W k j≠0}:ℝ))/175000≤(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  have hc : affineFeedingCard net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, W k j≠0} := by
    unfold affineFeedingCard
    exact Fintype.card_congr (Equiv.refl _)
  simpa only [hc] using affine_min_tradeoff hN net hmax

theorem exact_quadratic_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 3≤N)
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x, AffineSkipExtension.eval net x=Maximum N x)
    (hfeed : (Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, net.W k j≠0}:ℝ)≤(N:ℝ)^2) :
    (N:ℝ)^2/175000≤(h₂:ℝ) := by
  have hc : affineFeedingCard net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, net.W k j≠0} := by
    unfold affineFeedingCard
    exact Fintype.card_congr (Equiv.refl _)
  exact affine_quadratic_of_feeding_cap hN net hmax (by simpa only [hc] using hfeed)

theorem actual_max_three :
    ∃ net : AffineSkipNetwork 3 (firstWidth 3) (secondWidth 3),
      (∀ x, AffineSkipExtension.eval net x=Maximum 3 x) ∧
      (affineFeedingCard net:ℝ)≤(3:ℝ)^2 ∧
      (3:ℝ)^2/175000≤(secondWidth 3:ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net 3
  have hm : ∀ x, AffineSkipExtension.eval (ofOrdinary net) x=Maximum 3 x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hw : affineFeedingCard (ofOrdinary net)≤3^2 :=
    (affineFeedingCard_le _).trans (by norm_num [firstWidth,Nat.choose_two_right])
  have hwr : (affineFeedingCard (ofOrdinary net):ℝ)≤(3:ℝ)^2 := by exact_mod_cast hw
  exact ⟨ofOrdinary net,hm,hwr,affine_quadratic_of_feeding_cap (by decide : 3≤3) _ hm hwr⟩

#print axioms exact_raw_type
#print axioms exact_quadratic_type
#print axioms actual_max_three
end MaxCaterpillar.OvernightConstants.TradeoffTheta.Feeding.Check
