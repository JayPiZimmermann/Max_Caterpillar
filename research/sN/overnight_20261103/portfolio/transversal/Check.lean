import research.sN.overnight_20261103.portfolio.transversal.Bounds
import MaxCaterpillar.Frontier.Constructions

/-! Independent contracts expand the evaluator, support condition, and all
nine primitive real parameter arrays. A concrete exact MAX3 control follows. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.SupportTransversal.Check
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork AffineSkipExtension GrowingMatching

theorem raw_nine_arrays {N m h₁ h₂ : ℕ} [NeZero N] [NeZero m]
    (hm : 3 ≤ m) (e : Fin m ↪ Fin N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i*x i)+b j)) +
        (∑ i, U k i*x i)+θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i*x i)+b j)) +
        (∑ i, L i*x i)+β) = Maximum N x)
    (hkeep : ∀ j, b j=0 → (∑ i, A j i)=0 →
      (Finset.univ.filter fun i => A j i≠0) ⊆ Finset.univ.image e →
      (Finset.univ.filter fun i => A j i≠0).card ≤ 2) :
    (m:ℝ)^2 / 3000000 ≤ (h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact affine_retained_quadratic hm net hmax e hkeep

theorem literal_transversal {N m h₁ h₂ : ℕ} [NeZero N] [NeZero m]
    (hm : 3 ≤ m) (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (e : Fin m ↪ Fin N) (C : Finset (Fin N))
    (havoid : ∀ a, e a ∉ C)
    (hhit : ∀ j, net.b j=0 → (∑ i, net.A j i)=0 →
      3 ≤ (rowSupport (net.A j)).card →
      ∃ i ∈ rowSupport (net.A j), i ∈ C) :
    (m:ℝ)^2 / 3000000 ≤ (h₂:ℝ) :=
  affine_retained_quadratic hm net hmax e
    (braidOnRetained_of_transversal net e C havoid hhit)

theorem actual_max_three_control :
    ∃ net : AffineSkipNetwork 3 4 3,
      (∀ x, AffineSkipExtension.eval net x = Maximum 3 x) ∧
      BraidOnRetained net (Function.Embedding.refl (Fin 3)) ∧
      (3:ℝ)^2 / 3000000 ≤ (3:ℝ) := by
  let net := AffineSkipExtension.ofOrdinary maxThreeNet
  have hm : ∀ x, AffineSkipExtension.eval net x = Maximum 3 x := by
    intro x
    rw [AffineSkipExtension.eval_ofOrdinary, maxThreeNet_eval]
  have hk : BraidOnRetained net (Function.Embedding.refl (Fin 3)) := by
    intro j _ _ _
    have hs : rowSupport (net.A j) ⊆ (if j=0 then {0,2} else {1,2}) := by
      intro i hi
      fin_cases j <;> fin_cases i <;>
        norm_num [net, AffineSkipExtension.ofOrdinary, maxThreeNet,
          rowSupport, Fin.ext_iff] at *
    apply (Finset.card_le_of_subset hs).trans
    split_ifs <;> decide
  exact ⟨net, hm, hk, affine_retained_quadratic (by decide) net hm _ hk⟩

#check @raw_nine_arrays
#check @literal_transversal
#check @actual_max_three_control
#print axioms raw_nine_arrays
#print axioms literal_transversal
#print axioms actual_max_three_control
end MaxCaterpillar.Overnight.SupportTransversal.Check
