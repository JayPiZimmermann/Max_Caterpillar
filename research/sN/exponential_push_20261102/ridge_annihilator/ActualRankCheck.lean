import research.sN.exponential_push_20261102.ridge_annihilator.ActualRank
import MaxCaterpillar.Frontier.Constructions

/-! Independent statement driver: every primitive real array is explicit,
the target is the actual all-input maximum, and the conclusion uses the
original output coefficient and original weighted observation covectors. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.Ridge.Check
open BigOperators Frontier Frontier.RandomRestriction.AffineSkipExtension

theorem raw_nine_array_highrank {N h₁ h₂ : ℕ} [NeZero N]
    (hN : 3 ≤ N)
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (hmax : ∀ x : Point N,
      (∑ k, d k * relu
        ((∑ j, W k j * relu ((∑ i, A j i * x i) + b j)) +
          (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * relu ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x) :
    ∃ k : Fin h₂, d k ≠ 0 ∧
      N - 1 ≤ FiniteDimensional.finrank ℝ
        (LinearMap.range ((linMap (U k)).prod
          (LinearMap.pi fun j => W k j • linMap (A j)))) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact exists_active_original_second_highrank hN net hmax

/-- The smallest allowed arity has a concrete exact network satisfying the
premise, so the raw theorem is not checked only on an abstract identity. -/
example : ∃ k : Fin 3, (ofOrdinary maxThreeNet).d k ≠ 0 ∧
    2 ≤ FiniteDimensional.finrank ℝ
      (LinearMap.range (secondObservation (ofOrdinary maxThreeNet) k)) := by
  apply exists_active_original_second_highrank (by norm_num) (ofOrdinary maxThreeNet)
  intro x
  rw [eval_ofOrdinary,maxThreeNet_eval]

#check @raw_nine_array_highrank
#print axioms raw_nine_array_highrank
#print axioms exists_active_original_second_highrank
#print axioms maxThreeNet_eval
end MaxCaterpillar.ExponentialPush.Ridge.Check
