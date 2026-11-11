import MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff

/-! Independent contracts for the unconditional total-first-width bound.
The affine evaluator is expanded into its nine real parameter arrays/scalars.
No structural obstruction or numerical event estimate is a headline premise.
-/
set_option autoImplicit false
noncomputable section
namespace QuadraticCutoffCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open AffineSkipExtension GrowingMatching
attribute [local instance] Classical.propDecidable

-- The width assumption counts ALL original first hidden neurons.
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 3 ≤ N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x)
    (hwidth : (h₁ : ℝ) ≤ (N : ℝ)^2) :
    (1 / 10000000 : ℝ) * (N : ℝ)^2 ≤ (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A, b, W, U, θ, d, B, L, β⟩
  exact QuadraticCutoff.affine_quadratic hN net hmax hwidth

example {N h₁ h₂ : ℕ} [NeZero N] (hN : 3 ≤ N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x, net.eval x = Maximum N x) (hwidth : (h₁ : ℝ) ≤ (N : ℝ)^2) :
    (1 / 10000000 : ℝ) * (N : ℝ)^2 ≤ (h₂ : ℝ) :=
  QuadraticCutoff.normalized_quadratic hN net hn hmax hwidth

-- Both support budgets belong to one actual half model, retaining both
-- original index types and exactness on all real inputs.
example {N n h₁ h₂ : ℕ} [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x, net.eval x = Maximum N x) (hpair : 2 * n ≤ N) :
    ∃ S : Finset (Fin N), S.card = n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x = Maximum n x) ∧ model.TranslationNormalized ∧
      4 * ActualHalfRestriction.fourthMoment model ≤ 81 * h₁ ∧
      4 * ActualHalfRestriction.nonBraidCount model ≤ h₁ :=
  NormalizedTotalHalf.exists_model net hn hmax hpair

-- H(5,2) is supplied by an actual theorem, with no open-H hypothesis.
example (h₁ h₂ : ℕ) (net : NormalizedNetwork 5 h₁ h₂)
    (hn : net.TranslationNormalized)
    (hrows : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2)
    (hmax : ∀ x, net.eval x = Maximum 5 x) :
    ∃ r : Fin h₂,
      HasMatchingOn (braidInteractionGraph net hn r) 2 Finset.univ :=
  localMatchingObstruction_five_two h₁ h₂ net hn hrows hmax

example (m K : ℕ) (hm : 20000 ≤ m) (hKu : (K : ℝ) ≤ (m : ℝ) / 25)
    (M L : ℝ) (hM : M ≤ 2 * (m : ℝ)^2) (hL : L ≤ 100 * (m : ℝ)^2) :
    (1 / 2 : ℝ) ≤ 1 - 8 * (K : ℝ) / (m : ℝ) -
      M * 60 / ((m + 5).descFactorial 3 : ℝ) -
      L / ((m + 5).descFactorial 4 : ℝ) *
        ((K : ℝ)^2 * (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)) +
          10 * (K : ℝ)) :=
  QuadraticCutoff.coverage m K hm hKu M L hM hL

-- The rate is written out, rather than passed as an arbitrary constant.
example (m K : ℕ) (hm : 8 ≤ m) (hK : 0 < K) (hKu : (K : ℝ) ≤ (m : ℝ) / 25) :
    (120 : ℝ) / ((m + 5).descFactorial 4 : ℝ) *
      ((7 * (K : ℝ) / (24 * (m : ℝ) * ((m : ℝ) - 1)))^2)⁻¹ *
      Real.exp ((7 * (K : ℝ) / (24 * (m : ℝ) * ((m : ℝ) - 1))) *
        (5 * ((m : ℝ) + 4))) ≤ 1600 / (K : ℝ)^2 := by
  simpa only [tailRate] using QuadraticCutoff.envelope_le m K hm hK hKu

example {m h₁ h₂ : ℕ} [NeZero (m + 5)] (hm : 20000 ≤ m)
    (net : NormalizedNetwork (m + 5) h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x, net.eval x = Maximum (m + 5) x)
    (hM : (MaxCaterpillar.Frontier.RandomRestriction.BadFirst.largeSupportCount
      (firstSupports net) : ℝ) ≤ 2 * (m : ℝ)^2)
    (hL : (∑ j, ((firstSupports net j).card.descFactorial 4 : ℝ)) ≤ 100 * (m : ℝ)^2) :
    (m : ℝ)^2 / 2163200 ≤ (h₂ : ℝ) :=
  QuadraticCutoff.model_bound hm net hn hmax hM hL

private theorem actual_caterpillar_witness (N : ℕ) [NeZero N]
    (hN : 3 ≤ N) (hwidth : firstWidth N ≤ N^2) :
    ∃ net : AffineSkipNetwork N (firstWidth N) (secondWidth N),
      (∀ x, AffineSkipExtension.eval net x = Maximum N x) ∧
      (firstWidth N : ℝ) ≤ (N : ℝ)^2 ∧
      (1 / 10000000 : ℝ) * (N : ℝ)^2 ≤ (secondWidth N : ℝ) := by
  obtain ⟨net, hnet, _hrational, _hzeroBias⟩ := caterpillar_net N
  have hm : ∀ x, AffineSkipExtension.eval (ofOrdinary net) x = Maximum N x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hw : (firstWidth N : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast hwidth
  exact ⟨ofOrdinary net, hm, hw, QuadraticCutoff.affine_quadratic hN _ hm hw⟩

-- Boundary dimension, in the branch discharged by the linear theorem.
example : ∃ net : AffineSkipNetwork 3 (firstWidth 3) (secondWidth 3),
    (∀ x, AffineSkipExtension.eval net x = Maximum 3 x) ∧
    (firstWidth 3 : ℝ) ≤ (3 : ℝ)^2 ∧
    (1 / 10000000 : ℝ) * (3 : ℝ)^2 ≤ (secondWidth 3 : ℝ) := by
  apply actual_caterpillar_witness 3 (by decide)
  rw [firstWidth, Nat.choose_two_right]
  norm_num

-- First odd dimension beyond the small-dimension linear branch. The exact
-- second width remains symbolic; no Catalan/factorial expansion is performed.
example : ∃ net : AffineSkipNetwork 50001 (firstWidth 50001) (secondWidth 50001),
    (∀ x, AffineSkipExtension.eval net x = Maximum 50001 x) ∧
    (firstWidth 50001 : ℝ) ≤ (50001 : ℝ)^2 ∧
    (1 / 10000000 : ℝ) * (50001 : ℝ)^2 ≤ (secondWidth 50001 : ℝ) := by
  apply actual_caterpillar_witness 50001 (by decide)
  rw [firstWidth, Nat.choose_two_right]
  norm_num

#check @QuadraticCutoff.model_bound
#check @QuadraticCutoff.normalized_quadratic
#check @QuadraticCutoff.affine_quadratic
#print axioms QuadraticCutoff.coverage
#print axioms QuadraticCutoff.envelope_le
#print axioms QuadraticCutoff.model_bound
#print axioms QuadraticCutoff.normalized_quadratic
#print axioms QuadraticCutoff.affine_quadratic
#print axioms GrowingMatching.localMatchingObstruction_five_two
#print axioms NormalizedTotalHalf.exists_model
end QuadraticCutoffCheck
