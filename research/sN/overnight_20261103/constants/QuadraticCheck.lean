import research.sN.overnight_20261103.constants.Quadratic

/-! Independent semantic contracts for the unconditional650000 constant.
The headline uses all nine original real parameter arrays/scalars and counts
the TOTAL first hidden width. It assumes exactness at every real input.
The large-arity witness exercises the odd half restriction branch. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.OvernightConstants.Check
open BigOperators Frontier Frontier.RandomRestriction
open AffineSkipExtension GrowingMatching
attribute [local instance] Classical.propDecidable

/-- Literal raw-array type: arbitrary biases and both affine skips. -/
theorem raw_nine_array_contract {N h₁ h₂ : ℕ} [NeZero N] (hN : 3 ≤ N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x)
    (hwidth : (h₁ : ℝ) ≤ (N : ℝ)^2) :
    (1 / 650000 : ℝ) * (N : ℝ)^2 ≤ (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A, b, W, U, θ, d, B, L, β⟩
  exact affine_quadratic hN net hmax hwidth

theorem normalized_contract {N h₁ h₂ : ℕ} [NeZero N] (hN : 3 ≤ N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x, net.eval x = Maximum N x) (hwidth : (h₁ : ℝ) ≤ (N : ℝ)^2) :
    (1 / 650000 : ℝ) * (N : ℝ)^2 ≤ (h₂ : ℝ) :=
  normalized_quadratic hN net hn hmax hwidth

/-- The first and second hidden indices of the actual localized model are
the same as those of the original model; no statistical premise is supplied. -/
theorem actual_half_contract {N n h₁ h₂ : ℕ} [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x, net.eval x = Maximum N x) (hpair : 2*n ≤ N) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      16*(∑ j, (NormalizedNetwork.rowSupport (model.A j)).card.descFactorial 4) ≤ 105*h₁ :=
  Overnight.Constants.FallingHalf.exists_model net hn hmax hpair

/-- The only local structural obstruction consumed by the proof is already
proved over all real coefficients, including cancellation and free skips. -/
theorem five_input_obstruction (h₁ h₂ : ℕ) (net : NormalizedNetwork 5 h₁ h₂)
    (hn : net.TranslationNormalized)
    (hrows : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2)
    (hmax : ∀ x, net.eval x=Maximum 5 x) :
    ∃ r : Fin h₂, HasMatchingOn (braidInteractionGraph net hn r) 2 Finset.univ :=
  localMatchingObstruction_five_two h₁ h₂ net hn hrows hmax

private theorem actual_caterpillar_witness (N : ℕ) [NeZero N]
    (hN : 3 ≤ N) (hwidth : firstWidth N ≤ N^2) :
    ∃ net : AffineSkipNetwork N (firstWidth N) (secondWidth N),
      (∀ x, AffineSkipExtension.eval net x=Maximum N x) ∧
      (firstWidth N : ℝ) ≤ (N : ℝ)^2 ∧
      (1/650000 : ℝ)*(N : ℝ)^2 ≤ (secondWidth N : ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net N
  have hm : ∀ x, AffineSkipExtension.eval (ofOrdinary net) x=Maximum N x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hw : (firstWidth N : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast hwidth
  exact ⟨ofOrdinary net,hm,hw,affine_quadratic hN _ hm hw⟩

theorem smallest_arity_nonvacuity :
    ∃ net : AffineSkipNetwork 3 (firstWidth 3) (secondWidth 3),
      (∀ x, AffineSkipExtension.eval net x=Maximum 3 x) ∧
      (firstWidth 3 : ℝ) ≤ (3 : ℝ)^2 ∧
      (1/650000 : ℝ)*(3 : ℝ)^2 ≤ (secondWidth 3 : ℝ) := by
  apply actual_caterpillar_witness 3 (by decide)
  rw [firstWidth,Nat.choose_two_right]
  norm_num

/-- First odd arity beyond the linear branch: no huge second-width value is
expanded or computed, so this checks the actual hypothesis class. -/
theorem odd_large_arity_nonvacuity :
    ∃ net : AffineSkipNetwork 250001 (firstWidth 250001) (secondWidth 250001),
      (∀ x, AffineSkipExtension.eval net x=Maximum 250001 x) ∧
      (firstWidth 250001 : ℝ) ≤ (250001 : ℝ)^2 ∧
      (1/650000 : ℝ)*(250001 : ℝ)^2 ≤ (secondWidth 250001 : ℝ) := by
  apply actual_caterpillar_witness 250001 (by decide)
  rw [firstWidth,Nat.choose_two_right]
  norm_num

#check @raw_nine_array_contract
#print axioms raw_nine_array_contract
#print axioms normalized_contract
#print axioms actual_half_contract
#print axioms five_input_obstruction
#print axioms smallest_arity_nonvacuity
#print axioms odd_large_arity_nonvacuity
end MaxCaterpillar.OvernightConstants.Check
