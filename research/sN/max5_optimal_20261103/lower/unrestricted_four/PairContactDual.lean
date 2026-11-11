import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic

/-!
An elementary dual obstruction for two convex zero cones covering all
two-coordinate contact cones.  This is a finite-vector statement, not a
claim about network widths or an unformalized network reduction.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Max5.PairContactDual

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- A nonzero zero-sum real vector has a negative coordinate. -/
lemma exists_neg_of_sum_zero (a : ι → ℝ) (ha : ∑ i, a i = 0) (hne : a ≠ 0) :
    ∃ i, a i < 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hz : ∀ i, a i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => hn j)).mp ha i (Finset.mem_univ i)
  exact hne (funext hz)

/-- No nonnegative combination of two coordinate pairs lies in the
strictly negative quadrant.  Zero weights and repeated indices are allowed. -/
def NoNegativePair (a b : ι → ℝ) : Prop :=
  ∀ i j (s t : ℝ), 0 ≤ s → 0 ≤ t →
    ¬ (s * a i + t * a j < 0 ∧ s * b i + t * b j < 0)

lemma positive_second_at_negative_first (a b : ι → ℝ)
    (hb : ∑ i, b i = 0) (hbne : b ≠ 0) (hpair : NoNegativePair a b)
    {i : ι} (hai : a i < 0) : 0 < b i := by
  obtain ⟨j, hbj⟩ := exists_neg_of_sum_zero b hb hbne
  by_contra hbi
  have hbi' : b i ≤ 0 := le_of_not_gt hbi
  have hs : 0 < |a j| + 1 := by linarith [abs_nonneg (a j)]
  have ht : 0 < -a i := neg_pos.mpr hai
  apply hpair i j (|a j| + 1) (-a i) hs.le ht.le
  constructor
  · have hp : 0 < |a j| + 1 - a j := by linarith [le_abs_self (a j)]
    have hm := mul_neg_of_neg_of_pos hai hp
    nlinarith only [hm]
  · have h1 := mul_nonpos_of_nonneg_of_nonpos hs.le hbi'
    have h2 := mul_neg_of_pos_of_neg ht hbj
    linarith only [h1, h2]

/-- Two nonzero zero-sum vectors whose two-coordinate contact cones avoid
the negative quadrant are strictly negatively proportional. -/
theorem negatively_proportional (a b : ι → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (hane : a ≠ 0) (hbne : b ≠ 0) (hpair : NoNegativePair a b) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, b i = -c * a i := by
  classical
  let S : Finset ι := Finset.univ.filter fun i => a i < 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := exists_neg_of_sum_zero a ha hane
    exact ⟨i, by simp [S, hi]⟩
  obtain ⟨p, hpS, hpmin⟩ := S.exists_min_image (fun i => b i / (-a i)) hS
  have hap : a p < 0 := (Finset.mem_filter.mp hpS).2
  have hbp : 0 < b p := positive_second_at_negative_first a b hb hbne hpair hap
  have hcoord : ∀ i, 0 ≤ b p * a i - a p * b i := by
    intro i
    by_cases hai : a i < 0
    · have hiS : i ∈ S := by simp [S, hai]
      have hr := hpmin i hiS
      have hcross := (div_le_div_iff (neg_pos.mpr hap) (neg_pos.mpr hai)).mp hr
      nlinarith only [hcross]
    · have hai' : 0 ≤ a i := le_of_not_gt hai
      by_cases hbi : 0 ≤ b i
      · exact sub_nonneg.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg hap.le hbi)
          (mul_nonneg hbp.le hai'))
      · by_contra hdet
        have hd : b p * a i - a p * b i < 0 := lt_of_not_ge hdet
        let e : ℝ := -(b p * a i - a p * b i) / (2 * b p)
        have he : 0 < e := div_pos (neg_pos.mpr hd) (by positivity)
        have heq : e * (2 * b p) = -(b p * a i - a p * b i) := by
          dsimp [e]
          exact div_mul_cancel _ (ne_of_gt (by positivity : 0 < 2 * b p))
        apply hpair p i (a i + e) (-a p) (by linarith) (neg_nonneg.mpr hap.le)
        constructor
        · have hm := mul_neg_of_pos_of_neg he hap
          nlinarith only [hm]
        · nlinarith only [heq, hd]
  have hsum : ∑ i, (b p * a i - a p * b i) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha, hb]
    ring
  have hz : ∀ i, b p * a i - a p * b i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hcoord j)).mp
      hsum i (Finset.mem_univ i)
  refine ⟨b p / (-a p), div_pos hbp (neg_pos.mpr hap), fun i => ?_⟩
  have hpne : a p ≠ 0 := ne_of_lt hap
  calc
    b i = (-(b p * a i)) / (-a p) :=
      (eq_div_iff (neg_ne_zero.mpr hpne)).2 (by nlinarith only [hz i])
    _ = -(b p / (-a p)) * a i := by ring

/-- Includes the zero-vector degeneracies and needs no nonempty-index
assumption: if the index type is empty, both vectors are zero. -/
theorem zero_or_negatively_proportional (a b : ι → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hpair : NoNegativePair a b) :
    a = 0 ∨ b = 0 ∨ ∃ c : ℝ, 0 < c ∧ ∀ i, b i = -c * a i := by
  by_cases hane : a = 0
  · exact Or.inl hane
  by_cases hbne : b = 0
  · exact Or.inr (Or.inl hbne)
  exact Or.inr (Or.inr (negatively_proportional a b ha hb hane hbne hpair))

/-- A positive scalar multiple of the opposite vector supplies a nonvacuous
family satisfying the contact condition. -/
lemma noNegativePair_of_opposite (a : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    NoNegativePair a (fun i => -c * a i) := by
  intro i j s t _ _ h
  have hm := mul_neg_of_pos_of_neg hc h.1
  have hh : -(c * (s * a i + t * a j)) < 0 := by
    calc
      -(c * (s * a i + t * a j)) = s * (-c * a i) + t * (-c * a j) := by ring
      _ < 0 := h.2
  linarith only [hm, hh]

/-- Exact classification of the two-coordinate condition for zero-sum
vectors, with both zero degeneracies retained. -/
theorem noNegativePair_iff (a b : ι → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) :
    NoNegativePair a b ↔
      a = 0 ∨ b = 0 ∨ ∃ c : ℝ, 0 < c ∧ ∀ i, b i = -c * a i := by
  constructor
  · exact zero_or_negatively_proportional a b ha hb
  · intro h
    rcases h with rfl | rfl | ⟨c, hc, h⟩
    · intro i j s t _ _ hn
      simpa using hn.1
    · intro i j s t _ _ hn
      simpa using hn.2
    · have heq : b = fun i => -c * a i := funext h
      rw [heq]
      exact noNegativePair_of_opposite a c hc

#check @zero_or_negatively_proportional
#print axioms negatively_proportional
#print axioms zero_or_negatively_proportional
#check @noNegativePair_iff
#print axioms noNegativePair_iff

end MaxCaterpillar.Max5.PairContactDual
