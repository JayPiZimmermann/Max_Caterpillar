import MaxCaterpillar.Frontier.Basic
import Mathlib.Tactic

/-! Direct continuous curvature-score algebra. The geometric independence
of crossing hyperplanes remains in the accompanying paper-ready note. -/
namespace NaturalEightContinuous
open MaxCaterpillar BigOperators

noncomputable def score (A B D : ℝ) : ℝ :=
  relu (A+B) - relu A - relu D + relu (D-B)

lemma relu_abs (x : ℝ) : relu x = (x+|x|)/2 := by
  rcases le_total 0 x with h | h
  · simp [relu, max_eq_right h, abs_of_nonneg h]
  · simp [relu, max_eq_left h, abs_of_nonpos h]

lemma score_abs (A B D : ℝ) :
    score A B D = (|A+B|-|A|-|D|+|D-B|)/2 := by
  unfold score
  simp_rw [relu_abs]
  ring

lemma score_scale (t A B D : ℝ) :
    score (t*A) (t*B) (t*D) = |t| * score A B D := by
  rw [score_abs, score_abs]
  rw [show t*A+t*B=t*(A+B) by ring, show t*D-t*B=t*(D-B) by ring]
  simp only [abs_mul]
  ring

lemma score_fixed_positive {A B D : ℝ}
    (h0 : 0 ≤ A) (h1 : 0 ≤ A+B) (h2 : 0 ≤ D) (h3 : 0 ≤ D-B) :
    score A B D = 0 := by
  unfold score
  simp only [relu, max_eq_right h0, max_eq_right h1,
    max_eq_right h2, max_eq_right h3]
  ring

lemma score_fixed_negative {A B D : ℝ}
    (h0 : A ≤ 0) (h1 : A+B ≤ 0) (h2 : D ≤ 0) (h3 : D-B ≤ 0) :
    score A B D = 0 := by
  simp [score, relu, max_eq_left h0, max_eq_left h1,
    max_eq_left h2, max_eq_left h3]

lemma rectangle_identity (A B C D F : ℝ) :
    score A B D - score A B F - score C B D + score C B F = 0 := by
  unfold score
  ring

lemma score_target : score 0 1 0 = 1 := by norm_num [score, relu]

/-- No finite signed collection of units gives the target's four scores. -/
theorem no_finite_target_scores {ι : Type*} (J : Finset ι)
    (w A B C D F : ι → ℝ)
    (h00 : ∑ i in J, w i * score (A i) (B i) (D i) = 0)
    (h02 : ∑ i in J, w i * score (A i) (B i) (F i) = 0)
    (h20 : ∑ i in J, w i * score (C i) (B i) (D i) = 0)
    (h22 : ∑ i in J, w i * score (C i) (B i) (F i) = 1) : False := by
  have hsum : ∑ i in J, w i *
      (score (A i) (B i) (D i) - score (A i) (B i) (F i) -
       score (C i) (B i) (D i) + score (C i) (B i) (F i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    rw [rectangle_identity, mul_zero]
  simp_rw [mul_add, mul_sub] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, h00, h02, h20, h22] at hsum
  norm_num at hsum

#print axioms no_finite_target_scores
#print axioms score_scale
end NaturalEightContinuous
