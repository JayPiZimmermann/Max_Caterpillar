import Mathlib.Tactic

/-! Algebraic core of the all-finite-width corner-curvature obstruction.
The geometric normalization and the independence of crossing hyperplanes
are proved in the accompanying note, not in this leaf. -/

namespace NaturalEightRectangle

open BigOperators

noncomputable def score (x y : ℝ) : ℝ :=
  (if 0 ≤ x then 1 else 0) - (if 1 ≤ y then 1 else 0)

lemma score_fixed_positive {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    score x y = 0 := by simp [score, hx, hy]

lemma score_fixed_negative {x y : ℝ} (hx : x ≤ -1) (hy : y ≤ 0) :
    score x y = 0 := by
  have hx' : ¬ 0 ≤ x := by linarith
  have hy' : ¬ 1 ≤ y := by linarith
  simp [score, hx', hy']

lemma rectangle_identity (a c b d : ℝ) :
    score a b - score a d - score c b + score c d = 0 := by
  unfold score
  ring

lemma score_target : score 0 0 = 1 := by norm_num [score]

/-- Arbitrary finite signed collections cannot have the four target scores.
No bound or sign assumption is imposed on the coefficient functions. -/
theorem no_finite_target_scores {ι : Type*} (J : Finset ι)
    (w a c b d : ι → ℝ)
    (h00 : ∑ i in J, w i * score (a i) (b i) = 0)
    (h02 : ∑ i in J, w i * score (a i) (d i) = 0)
    (h20 : ∑ i in J, w i * score (c i) (b i) = 0)
    (h22 : ∑ i in J, w i * score (c i) (d i) = 1) : False := by
  have hsum : ∑ i in J, w i *
      (score (a i) (b i) - score (a i) (d i) -
       score (c i) (b i) + score (c i) (d i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    rw [rectangle_identity, mul_zero]
  simp_rw [mul_add, mul_sub] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, h00, h02, h20, h22] at hsum
  norm_num at hsum

#print axioms no_finite_target_scores

end NaturalEightRectangle
