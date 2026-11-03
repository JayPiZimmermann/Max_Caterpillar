import research.sN.overnight_20261103.constants.tradeoff_theta.Min

/-! Independent expanded raw-parameter contract and a realizable MAX3 control. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta.Check
open BigOperators Frontier Frontier.RandomRestriction AffineSkipExtension

/-- Every parameter is an ordinary real array; all real inputs are quantified.
There is no cap on either hidden width and no structural hypothesis. -/
theorem exact_raw_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 3≤N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x) :
    min ((N:ℝ)^2) ((N:ℝ)^4/(h₁:ℝ))/175000≤(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact affine_min_tradeoff hN net hmax

theorem exact_scaled_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 3≤N)
    (net : AffineSkipNetwork N h₁ h₂) (C : ℝ) (hC : 1≤C)
    (hmax : ∀ x, AffineSkipExtension.eval net x=Maximum N x)
    (hw : (h₁:ℝ)≤C*(N:ℝ)^2) :
    (N:ℝ)^2/(175000*C)≤(h₂:ℝ) :=
  affine_scaled hN net C hC hmax hw

/-- Actual network nonvacuity at the smallest advertised arity. -/
theorem actual_max_three :
    ∃ net : AffineSkipNetwork 3 (firstWidth 3) (secondWidth 3),
      (∀ x, AffineSkipExtension.eval net x=Maximum 3 x) ∧
      min ((3:ℝ)^2) ((3:ℝ)^4/(firstWidth 3:ℝ))/175000≤(secondWidth 3:ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net 3
  have hm : ∀ x, AffineSkipExtension.eval (ofOrdinary net) x=Maximum 3 x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  exact ⟨ofOrdinary net,hm,affine_min_tradeoff (by decide : 3≤3) (ofOrdinary net) hm⟩

/-- A scale can exceed any fixed constant; the argument is not restricted to
an asymptotic quadratic-width family. -/
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 3≤N)
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x, AffineSkipExtension.eval net x=Maximum N x)
    (hw : (h₁:ℝ)≤(N:ℝ)^3) :
    (N:ℝ)/175000≤(h₂:ℝ) := by
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith only [hNr]
  have hs := affine_scaled hN net (N:ℝ) (by linarith only [hNr]) hmax
    (by nlinarith only [hw])
  have heq : (N:ℝ)^2/(175000*(N:ℝ))=(N:ℝ)/175000 := by
    field_simp [hn0.ne']
    <;> ring
  rwa [heq] at hs

#print axioms exact_raw_type
#print axioms exact_scaled_type
#print axioms actual_max_three
end MaxCaterpillar.OvernightConstants.TradeoffTheta.Check
