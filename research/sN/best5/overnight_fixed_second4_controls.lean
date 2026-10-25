import Mathlib

/- Elementary exact controls for the second-width-four equality analysis.
   These do not state or prove a new network lower bound. -/
namespace OvernightSecondFour

 theorem no_linear_pair_selector (a b c d : ℝ) :
    ¬ (∀ w x y z : ℝ,
      min (max w x) (max y z) ≤ a*w+b*x+c*y+d*z ∧
      a*w+b*x+c*y+d*z ≤ max (max w x) (max y z)) := by
  intro h
  have ha := h (-1) 0 0 0
  have hb := h 0 (-1) 0 0
  have hc := h 0 0 (-1) 0
  have hd := h 0 0 0 (-1)
  have he := h 1 1 1 1
  norm_num at ha hb hc hd he
  linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, hd.1, hd.2, he.1]

 theorem diamond_bound (a b p q : ℝ) (h : |a| + |b| ≤ 1) :
    |a*p+b*q| ≤ max |p| |q| := by
  have hp := le_max_left |p| |q|
  have hq := le_max_right |p| |q|
  have hM : 0 ≤ max |p| |q| := le_trans (abs_nonneg p) hp
  calc
    |a*p+b*q| ≤ |a*p|+|b*q| := abs_add _ _
    _ = |a| * |p| + |b| * |q| := by rw [abs_mul, abs_mul]
    _ ≤ (|a|+|b|) * max |p| |q| := by
      nlinarith [abs_nonneg a, abs_nonneg b]
    _ ≤ max |p| |q| := by nlinarith

#print axioms no_linear_pair_selector
#print axioms diamond_bound
end OvernightSecondFour
