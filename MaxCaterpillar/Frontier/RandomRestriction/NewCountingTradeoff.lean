import MaxCaterpillar.Frontier.RandomRestriction.SharperTradeoff

/-!
# Scalar assembly with an explicit per-neuron counting constant

The parameter D is the still-needed per-neuron probability constant. The
old counting input is exactly the instance D=31200000. The proposed
size-bias replacement aims to establish D=400 for actual networks; this
file does not assume that replacement has been proved for a network.
-/
set_option autoImplicit false

namespace MaxCaterpillar.NewCountingTradeoff
open WeightedTradeoff

def CountingPrerequisite (D m A W : ℝ) : Prop :=
  ∀ K : ℕ, 4 ≤ K → (K : ℝ) ≤ m / 100 →
    16 * A * (K : ℝ) ^ 2 ≤ m ^ 4 →
    (42 / 100 : ℝ) * (K : ℝ) ^ 2 ≤ D * W

theorem original_prerequisite (m A W : ℝ) :
    CountingPrerequisite 31200000 m A W ↔ WeightedCountingPrerequisite m A W :=
  Iff.rfl

theorem counting_implies_raw_bound (D m A W : ℝ)
    (hD : 2 ≤ D) (hm : 400 ≤ m) (hA : 1 ≤ A) (hW : 1 ≤ W)
    (hcount : CountingPrerequisite D m A W) :
    (21 / 200 : ℝ) * min (m ^ 2 / 10000) (m ^ 4 / (16 * A)) ≤ D * W := by
  let q := min (m ^ 2 / 10000) (m ^ 4 / (16 * A))
  have hmp : 0 < m := by linarith only [hm]
  have hAp : 0 < A := by linarith only [hA]
  have hq : 0 ≤ q := le_min (by positivity) (by positivity)
  let x := Real.sqrt q
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = q := Real.sq_sqrt hq
  by_cases hx : 4 ≤ x
  · let K := ⌊x⌋₊
    obtain ⟨hlower, hK4⟩ := floor_half_bound x hx
    have hKupper : (K : ℝ) ≤ x := Nat.floor_le hx0
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hKsq : (K : ℝ) ^ 2 ≤ q := by nlinarith only [hKupper, hK0, hxsq]
    have hq1 : q ≤ m ^ 2 / 10000 := min_le_left _ _
    have hq2 : q ≤ m ^ 4 / (16 * A) := min_le_right _ _
    have hcut : (K : ℝ) ≤ m / 100 := by nlinarith only [hKsq, hq1, hmp]
    have hbudget : 16 * A * (K : ℝ) ^ 2 ≤ m ^ 4 := by
      have hh := (le_div_iff (by positivity : 0 < 16 * A)).mp (hKsq.trans hq2)
      nlinarith only [hh]
    have hc := hcount K hK4 hcut hbudget
    have hsqLower : q ≤ 4 * (K : ℝ) ^ 2 := by
      nlinarith only [hlower, hxsq, hK0, hx0]
    change (21 / 200 : ℝ) * q ≤ D * W
    nlinarith only [hc, hsqLower]
  · have hx4 : x < 4 := lt_of_not_ge hx
    have hq16 : q < 16 := by nlinarith only [hx4, hx0, hxsq]
    have hDW : 2 ≤ D * W := by
      have hh := mul_le_mul_of_nonneg_left hW (by linarith only [hD] : 0 ≤ D)
      nlinarith only [hh, hD]
    change (21 / 200 : ℝ) * q ≤ D * W
    nlinarith only [hDW, hq16]

theorem counting_implies_tradeoff (D N n h A W : ℝ)
    (hD : 2 ≤ D) (hN : 0 ≤ N) (hn : 520 ≤ n) (hhalf : N ≤ 3 * n)
    (hA : 1 ≤ A) (hmoment : 4 * A ≤ 81 * h) (hW : 1 ≤ W)
    (hcount : CountingPrerequisite D (n - 5) A W) :
    (21 / 20000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ D * W := by
  have hraw := counting_implies_raw_bound D (n - 5) A W hD
    (by linarith only [hn]) hA hW hcount
  have hcompare := SharperTradeoff.compare_raw_cutoff N n h A hN hn hhalf hA hmoment
  nlinarith only [hraw, hcompare]

/-- This is conditional on the new numerical counting input, not a proof
that actual networks satisfy the proposed size-bias estimate. -/
theorem four_hundred_tradeoff (N n h A W : ℝ)
    (hN : 0 ≤ N) (hn : 520 ≤ n) (hhalf : N ≤ 3 * n)
    (hA : 1 ≤ A) (hmoment : 4 * A ≤ 81 * h) (hW : 1 ≤ W)
    (hcount : CountingPrerequisite 400 (n - 5) A W) :
    (1 / 400000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ W := by
  have hc := counting_implies_tradeoff 400 N n h A W (by norm_num)
    hN hn hhalf hA hmoment hW hcount
  have hh : 0 < h := by linarith only [hA, hmoment]
  have hT : 0 ≤ min (N ^ 2) (N ^ 4 / h) :=
    le_min (sq_nonneg N) (div_nonneg (pow_nonneg hN 4) hh.le)
  nlinarith only [hc, hT]

theorem linear_absorption (N h W : ℝ)
    (hN : 1040 ≤ N) (hwidth : N ^ 3 < 1000 * h)
    (hlinear : N ≤ 2 * W + 2) :
    (1 / 400000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ W := by
  have hNp : 0 < N := by linarith only [hN]
  have hhp : 0 < h := by nlinarith only [hwidth, pow_pos hNp 3]
  have hratio : N ^ 4 / h ≤ 1000 * N := by
    apply (div_le_iff hhp).mpr
    have hm := mul_le_mul_of_nonneg_left hwidth.le hNp.le
    nlinarith only [hm]
  have hmin := (min_le_right (N ^ 2) (N ^ 4 / h)).trans hratio
  nlinarith only [hmin, hlinear, hN]

#print axioms counting_implies_raw_bound
#print axioms counting_implies_tradeoff
#print axioms four_hundred_tradeoff
#print axioms linear_absorption

end MaxCaterpillar.NewCountingTradeoff
