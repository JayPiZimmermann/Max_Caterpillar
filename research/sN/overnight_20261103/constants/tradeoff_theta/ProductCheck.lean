import research.sN.overnight_20261103.constants.tradeoff_theta.Product

/-! Independent contracts and realizable boundary controls for width products. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta.ProductCheck
open BigOperators Frontier Frontier.RandomRestriction AffineSkipExtension

theorem exact_raw_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 15≤N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x) :
    (N:ℝ)^4/700000≤(h₁:ℝ)*(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact affine_width_product hN net hmax

theorem exact_ordinary_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 6≤N)
    (net : Network N h₁ h₂) (hmax : ∀ x,net.eval x=Maximum N x) :
    (N:ℝ)^4/700000≤(h₁:ℝ)*(h₂:ℝ) := ordinary_width_product hN net hmax

theorem actual_max_six :
    ∃ net : Network 6 (firstWidth 6) (secondWidth 6),
      (∀ x,net.eval x=Maximum 6 x) ∧
      (6:ℝ)^4/700000≤(firstWidth 6:ℝ)*(secondWidth 6:ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net 6
  exact ⟨net,hnet,ordinary_width_product (by decide : 6≤6) net hnet⟩

theorem actual_affine_max_fifteen :
    ∃ net : AffineSkipNetwork 15 (firstWidth 15) (secondWidth 15),
      (∀ x,AffineSkipExtension.eval net x=Maximum 15 x) ∧
      (15:ℝ)^4/700000≤(firstWidth 15:ℝ)*(secondWidth 15:ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net 15
  have hm : ∀ x,AffineSkipExtension.eval (ofOrdinary net) x=Maximum 15 x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  exact ⟨ofOrdinary net,hm,affine_width_product (by decide : 15≤15) (ofOrdinary net) hm⟩

#print axioms exact_raw_type
#print axioms exact_ordinary_type
#print axioms actual_max_six
#print axioms actual_affine_max_fifteen
end MaxCaterpillar.OvernightConstants.TradeoffTheta.ProductCheck
