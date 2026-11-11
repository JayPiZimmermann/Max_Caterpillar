import MaxCaterpillar.Frontier.RandomRestriction.FeedingSharp

/-! Independent contracts for the improved full affine-skip lower bound.
The network formula and original feeding denominator are expanded here;
the numerical contracts are stated independently of the producer's helpers.
-/
set_option autoImplicit false
noncomputable section
namespace AffineFeedingSharpCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction FeedingCore AffineSkipExtension
attribute [local instance] Classical.propDecidable

example {N h₁ h₂ : ℕ} (net : AffineSkipNetwork N h₁ h₂) :
    affineFeedingCard net =
      Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, net.W k j ≠ 0} := by
  unfold affineFeedingCard
  exact Fintype.card_congr (Equiv.refl _)

-- All nine parameter arrays/scalars are unrestricted real parameters.
-- The only functional hypothesis is exact MAX on every real input.
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040 ≤ N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, d k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, U k i * x i) + θ k)) +
      ((∑ j, B j * max 0 ((∑ i, A j i * x i) + b j)) +
        (∑ i, L i * x i) + β) = Maximum N x) :
    (1 / 40000000 : ℝ) * min ((N : ℝ)^2)
      ((N : ℝ)^4 /
        (Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, W k j ≠ 0} : ℝ)) ≤ (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A, b, W, U, θ, d, B, L, β⟩
  have hc : affineFeedingCard net =
      Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, W k j ≠ 0} := by
    unfold affineFeedingCard
    exact Fintype.card_congr (Equiv.refl _)
  simpa only [hc] using FeedingSharp.affine_feeding_tradeoff hN net hmax

-- The quadratic corollary also uses the original W columns, including
-- columns whose first neurons disappear under later normalization.
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040 ≤ N)
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (hfeed :
      (Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, net.W k j ≠ 0} : ℝ) ≤ (N : ℝ)^2) :
    (1 / 40000000 : ℝ) * (N : ℝ)^2 ≤ (h₂ : ℝ) := by
  have hc : affineFeedingCard net =
      Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, net.W k j ≠ 0} := by
    unfold affineFeedingCard
    exact Fintype.card_congr (Equiv.refl _)
  exact FeedingSharp.affine_feeding_quadratic hN net hmax (by simpa only [hc] using hfeed)

-- The strengthened optimizer consumes the already established count;
-- no new geometric or probabilistic assertion is assumed here.
example (m A W : ℝ) (hm : 400 ≤ m) (hA : 1 ≤ A) (hW : 11 ≤ W)
    (hcount : ∀ K : ℕ, 4 ≤ K → (K : ℝ) ≤ m / 100 →
      16 * A * (K : ℝ)^2 ≤ m^4 →
      (42 / 100 : ℝ) * (K : ℝ)^2 ≤ 400 * W) :
    min (m^2 / 10000) (m^4 / (16 * A)) ≤ 975 * W :=
  FeedingSharp.counting_raw m A W hm hA hW hcount

example (N n h A : ℝ) (hN : 0 ≤ N) (hn : 520 ≤ n)
    (hhalf : N ≤ 2 * n + 1) (hA : 1 ≤ A) (hmoment : 4 * A ≤ 81 * h) :
    min (N^2) (N^4 / h) ≤
      41000 * min ((n - 5)^2 / 10000) ((n - 5)^4 / (16 * A)) :=
  FeedingSharp.compare_cutoff N n h A hN hn hhalf hA hmoment

-- A genuine exact nonlinear network at the boundary input dimension meets
-- the feeding-width condition and satisfies the stronger conclusion.
example : ∃ net : AffineSkipNetwork 1040 (firstWidth 1040) (secondWidth 1040),
    (∀ x, AffineSkipExtension.eval net x = Maximum 1040 x) ∧
    (affineFeedingCard net : ℝ) ≤ (1040 : ℝ)^2 ∧
    (1 / 40000000 : ℝ) * (1040 : ℝ)^2 ≤ (secondWidth 1040 : ℝ) := by
  obtain ⟨net, hnet, _hbias, _hrational⟩ := caterpillar_net 1040
  have hm : ∀ x, AffineSkipExtension.eval (ofOrdinary net) x = Maximum 1040 x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hw : affineFeedingCard (ofOrdinary net) ≤ 1040^2 :=
    (affineFeedingCard_le _).trans (by norm_num [firstWidth, Nat.choose_two_right])
  have hwr : (affineFeedingCard (ofOrdinary net) : ℝ) ≤ (1040 : ℝ)^2 := by
    exact_mod_cast hw
  exact ⟨ofOrdinary net, hm, hwr,
    FeedingSharp.affine_feeding_quadratic (by decide) _ hm hwr⟩

#check @FeedingSharp.normalized_feeding_tradeoff
#check @FeedingSharp.affine_feeding_tradeoff
#check @FeedingSharp.affine_feeding_quadratic
#print axioms FeedingSharp.counting_raw
#print axioms FeedingSharp.compare_cutoff
#print axioms FeedingSharp.forty_million_tradeoff
#print axioms FeedingSharp.linear_absorption
#print axioms FeedingSharp.normalized_feeding_tradeoff
#print axioms FeedingSharp.affine_feeding_tradeoff
#print axioms FeedingSharp.affine_feeding_quadratic
end AffineFeedingSharpCheck
