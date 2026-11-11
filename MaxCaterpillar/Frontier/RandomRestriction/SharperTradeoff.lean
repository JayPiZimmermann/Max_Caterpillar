import MaxCaterpillar.Frontier.RandomRestriction.WeightedTradeoff

/-!
# Retain the raw cutoff when transferring the paired restriction

This improves only the verified scalar assembly. The same weighted counting
prerequisite still has to be established for actual networks. Keeping its
two differently scaled cutoff terms avoids the loss from first replacing
them by a common coarse arity constant.
-/
set_option autoImplicit false

namespace MaxCaterpillar.SharperTradeoff
open WeightedTradeoff

lemma compare_raw_cutoff (N n h A : ℝ)
    (hN : 0 ≤ N) (hn : 520 ≤ n) (hhalf : N ≤ 3 * n)
    (hA : 1 ≤ A) (hmoment : 4 * A ≤ 81 * h) :
    min (N ^ 2) (N ^ 4 / h) ≤
      100000 * min ((n - 5) ^ 2 / 10000) ((n - 5) ^ 4 / (16 * A)) := by
  have hAp : 0 < A := by linarith only [hA]
  have hhp : 0 < h := by linarith only [hA, hmoment]
  have hm0 : 0 ≤ n - 5 := by linarith only [hn]
  have hline : N ≤ (31 / 10 : ℝ) * (n - 5) := by
    linarith only [hn, hhalf]
  have h2 : N ^ 2 ≤ 10 * (n - 5) ^ 2 := by
    have hs := mul_self_le_mul_self hN hline
    nlinarith only [hs, sq_nonneg (n - 5)]
  have h4 : N ^ 4 ≤ 100 * (n - 5) ^ 4 := by
    have hs := mul_self_le_mul_self (sq_nonneg N) h2
    nlinarith only [hs]
  by_cases hc : (n - 5) ^ 2 / 10000 ≤ (n - 5) ^ 4 / (16 * A)
  · rw [min_eq_left hc]
    exact (min_le_left _ _).trans (by nlinarith only [h2])
  · rw [min_eq_right (le_of_not_ge hc)]
    apply (min_le_right _ _).trans
    apply (div_le_iff hhp).mpr
    have hN4A := mul_le_mul_of_nonneg_right h4 hAp.le
    have hAm4 := mul_le_mul_of_nonneg_right hmoment (pow_nonneg hm0 4)
    have hprod : N ^ 4 * A ≤ 6250 * (n - 5) ^ 4 * h := by
      nlinarith only [hN4A, hAm4,
        mul_nonneg (pow_nonneg hm0 4) hhp.le]
    apply (mul_le_mul_right hAp).mp
    have hid : (100000 * ((n - 5) ^ 4 / (16 * A)) * h) * A =
        6250 * (n - 5) ^ 4 * h := by
      field_simp
      ring
    rw [hid]
    exact hprod

/-- A 330-fold improvement of the previous conservative scalar constant,
with exactly the same unproved network counting input. -/
theorem paired_counting_implies_tradeoff (N n h A W : ℝ)
    (hN : 0 ≤ N) (hn : 520 ≤ n) (hhalf : N ≤ 3 * n)
    (hA : 1 ≤ A) (hmoment : 4 * A ≤ 81 * h) (hW : 1 ≤ W)
    (hcount : WeightedCountingPrerequisite (n - 5) A W) :
    (33 / 1000000000000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ W := by
  have hraw := counting_implies_moment_bound (n - 5) A W
    (by linarith only [hn]) hA hW hcount
  have hcompare := compare_raw_cutoff N n h A hN hn hhalf hA hmoment
  nlinarith only [hraw, hcompare]

/-- The existing linear network bound still absorbs the complementary
large-first-width regime at the improved scalar constant. -/
theorem linear_bound_absorbs_large_first_width (N h W : ℝ)
    (hN : 1040 ≤ N) (hwidth : N ^ 3 < 1000 * h)
    (hlinear : N ≤ 2 * W + 2) :
    (33 / 1000000000000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ W := by
  have hNp : 0 < N := by linarith only [hN]
  have hhp : 0 < h := by nlinarith only [hwidth, pow_pos hNp 3]
  have hratio : N ^ 4 / h ≤ 1000 * N := by
    apply (div_le_iff hhp).mpr
    have hm := mul_le_mul_of_nonneg_left hwidth.le hNp.le
    nlinarith only [hm]
  have hmin := (min_le_right (N ^ 2) (N ^ 4 / h)).trans hratio
  nlinarith only [hmin, hlinear, hN]

#print axioms compare_raw_cutoff
#print axioms paired_counting_implies_tradeoff
#print axioms linear_bound_absorbs_large_first_width

end MaxCaterpillar.SharperTradeoff
