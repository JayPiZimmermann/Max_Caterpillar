import research.sN.max5_optimal_20261103.lower.triple_contact.TripleContact
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Max5Optimal.TripleContact

example : ∀ {N : ℕ} [NeZero N] {k : ℕ}
    (R : Point N → ℝ) (g : Fin k → Point N → ℝ) (d : Fin k → ℝ)
    (q : Point N) (I : Finset (Fin N)),
    3 ≤ I.card → (∀ i ∈ I, q i = 0) → (∀ i ∉ I, q i ≤ -1) →
    LocOddLin R q → (∀ j, LocOddLin (g j) q) → (∀ j, Continuous (g j)) →
    (∀ x, R x + ∑ j, d j * relu (g j x) = Maximum N x) →
    ∃ j, g j q = 0 := @exists_zero_core_at_top_tie

example : ∀ {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (βg cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (βh ch : Fin mh → ℝ),
    (∀ x, shallow aR bR AR βR cR x +
      relu (shallow ag bg Ag βg cg x) + relu (shallow ah bh Ah βh ch x) = Maximum 5 x) →
    ∀ (i j : Fin 5), i ≠ j →
    shallow ag bg Ag βg cg (-unitVec i - unitVec j) = 0 ∨
      shallow ah bh Ah βh ch (-unitVec i - unitVec j) = 0 := @max5_pair_contact

#print axioms exists_zero_core_at_top_tie
#print axioms max5_pair_contact

example : ∀ {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (βg cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (βh ch : Fin mh → ℝ),
    (∀ x, shallow aR bR AR βR cR x +
      relu (shallow ag bg Ag βg cg x) + relu (shallow ah bh Ah βh ch x) = Maximum 5 x) →
    ∀ (i j : Fin 5), i ≠ j → ∀ a b : ℝ, 0 < a → 0 < b →
    shallow ag bg Ag βg cg (-(a • unitVec i) - b • unitVec j) = 0 ∨
      shallow ah bh Ah βh ch (-(a • unitVec i) - b • unitVec j) = 0 := @max5_weighted_pair_contact

#print axioms max5_weighted_pair_contact
