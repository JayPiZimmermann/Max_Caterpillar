import Mathlib

/-!
# Scalar assembly for a weighted version of Jensen's counting argument

This file does not state a theorem about neural networks. Its explicit
`WeightedCountingPrerequisite` is the output still needed from the geometric,
certificate, and random-scale arguments. Only the subsequent optimization of
the integer cutoff and its constants is verified here.

The parameter A is a positive upper bound for the fourth support moment. Use
max(actual moment, 1) to include the case with no non-braid supports.
-/
set_option autoImplicit false

namespace MaxCaterpillar.WeightedTradeoff

/-- The weighted counting conclusion before optimizing the integer cutoff.
The good-event estimate is 4 A K²/m⁴ ≤ 1/4; the remaining event has probability
at least 0.42, and one neuron contributes at most 3.12e7/K².
This predicate is a prerequisite, not an assertion that those estimates hold
for a particular network. -/
def WeightedCountingPrerequisite (m A W : ℝ) : Prop :=
  ∀ K : ℕ, 4 ≤ K → (K : ℝ) ≤ m / 100 →
    16 * A * (K : ℝ) ^ 2 ≤ m ^ 4 →
    (42 / 100 : ℝ) * (K : ℝ) ^ 2 ≤ 31200000 * W

/-- Elementary floor loss used when the ideal cutoff is at least four. -/
lemma floor_half_bound (x : ℝ) (hx : 4 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ 4 ≤ ⌊x⌋₊ := by
  constructor
  · have h := Nat.lt_floor_add_one x
    have h4 : (4 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor hx
    have h4' : (4 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h4
    linarith
  · exact Nat.le_floor hx

/-- Optimizing the cutoff loses at most a factor four in its square.
The conclusion is deliberately conditional on the counting prerequisite. -/
theorem counting_implies_moment_bound (m A W : ℝ)
    (hm : 400 ≤ m) (hA : 1 ≤ A) (hW : 1 ≤ W)
    (hcount : WeightedCountingPrerequisite m A W) :
    (33 / 10000000000 : ℝ) *
      min (m ^ 2 / 10000) (m ^ 4 / (16 * A)) ≤ W := by
  let q := min (m ^ 2 / 10000) (m ^ 4 / (16 * A))
  have hmp : 0 < m := by linarith
  have hAp : 0 < A := by linarith
  have hq : 0 ≤ q := le_min (by positivity) (by positivity)
  let x := Real.sqrt q
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = q := Real.sq_sqrt hq
  by_cases hx : 4 ≤ x
  · let K := ⌊x⌋₊
    obtain ⟨hlower, hK4⟩ := floor_half_bound x hx
    have hKupper : (K : ℝ) ≤ x := Nat.floor_le hx0
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hKsq : (K : ℝ) ^ 2 ≤ q := by nlinarith
    have hq1 : q ≤ m ^ 2 / 10000 := min_le_left _ _
    have hq2 : q ≤ m ^ 4 / (16 * A) := min_le_right _ _
    have hcut : (K : ℝ) ≤ m / 100 := by nlinarith
    have hbudget : 16 * A * (K : ℝ) ^ 2 ≤ m ^ 4 := by
      have h := (le_div_iff (by positivity : 0 < 16 * A)).mp (hKsq.trans hq2)
      nlinarith only [h]
    have hc := hcount K hK4 hcut hbudget
    have hsqLower : q ≤ 4 * (K : ℝ) ^ 2 := by nlinarith
    change (33 / 10000000000 : ℝ) * q ≤ W
    nlinarith only [hc, hsqLower, hq]
  · have hx4 : x < 4 := lt_of_not_ge hx
    have hq16 : q < 16 := by nlinarith
    change (33 / 10000000000 : ℝ) * q ≤ W
    nlinarith only [hW, hq16]

/-- The five coordinates used for the obstruction only affect a constant. -/
lemma compare_full_arity (n A : ℝ) (hn : 510 ≤ n) (hA : 1 ≤ A) :
    min (n ^ 2) (n ^ 4 / A) ≤
      11000 * min ((n - 5) ^ 2 / 10000) ((n - 5) ^ 4 / (16 * A)) := by
  let m := n - 5
  have hn0 : 0 ≤ n := by linarith
  have hm0 : 0 ≤ m := by dsimp [m]; linarith
  have hnm : n ≤ (51 / 50 : ℝ) * m := by dsimp [m]; linarith
  have hnm2 := mul_self_le_mul_self hn0 hnm
  have hsquare : n ^ 2 ≤ (11 / 10 : ℝ) * m ^ 2 := by
    nlinarith only [hnm2, sq_nonneg m]
  have hnm' : n ≤ 2 * m := by dsimp [m]; linarith
  have hnm2' : n ^ 2 ≤ 4 * m ^ 2 := by
    nlinarith only [mul_self_le_mul_self hn0 hnm']
  have hnm4 : n ^ 4 ≤ 16 * m ^ 4 := by
    have h := mul_self_le_mul_self (sq_nonneg n) hnm2'
    nlinarith only [h]
  have hAp : 0 < A := by linarith
  change _ ≤ 11000 * min (m ^ 2 / 10000) (m ^ 4 / (16 * A))
  by_cases h : m ^ 2 / 10000 ≤ m ^ 4 / (16 * A)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by nlinarith only [hsquare])
  · rw [min_eq_right (le_of_not_ge h)]
    apply (min_le_right _ _).trans
    apply (div_le_iff hAp).mpr
    have hidentity : (11000 * (m ^ 4 / (16 * A))) * A =
        (11000 / 16 : ℝ) * m ^ 4 := by field_simp; ring
    rw [hidentity]
    exact hnm4.trans (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hm0 4))

/-- The verified scalar consequence of the as-yet-unproved weighted counting
input. This has no network hypothesis or implicit network conclusion. -/
theorem counting_implies_arity_tradeoff (n A W : ℝ)
    (hn : 510 ≤ n) (hA : 1 ≤ A) (hW : 1 ≤ W)
    (hcount : WeightedCountingPrerequisite (n - 5) A W) :
    (3 / 10000000000000 : ℝ) * min (n ^ 2) (n ^ 4 / A) ≤ W := by
  have hbound := counting_implies_moment_bound (n - 5) A W
    (by linarith) hA hW hcount
  have hcompare := compare_full_arity n A hn hA
  nlinarith only [hbound, hcompare]

/-- A conservative half-restriction transfer. The assumption N ≤ 3n covers
both parity cases for n = floor(N/2), N ≥ 3. -/
lemma half_restriction_transfer (N n h A W : ℝ)
    (hN : 0 ≤ N) (hn : 0 ≤ n) (hA : 1 ≤ A)
    (hhalf : N ≤ 3 * n) (hmoment : 4 * A ≤ 81 * h)
    (hlocal : (3 / 10000000000000 : ℝ) *
      min (n ^ 2) (n ^ 4 / A) ≤ W) :
    (1 / 10000000000000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ W := by
  have hhp : 0 < h := by linarith only [hA, hmoment]
  have hAp : 0 < A := by linarith
  have h2 : N ^ 2 ≤ 9 * n ^ 2 := by
    nlinarith only [mul_self_le_mul_self hN hhalf]
  have h4 : N ^ 4 ≤ 81 * n ^ 4 := by
    have hs := mul_self_le_mul_self (sq_nonneg N) h2
    nlinarith only [hs]
  have hcompare : min (N ^ 2) (N ^ 4 / h) ≤
      3000 * min (n ^ 2) (n ^ 4 / A) := by
    by_cases hcase : n ^ 2 ≤ n ^ 4 / A
    · rw [min_eq_left hcase]
      exact (min_le_left _ _).trans (by nlinarith only [h2, sq_nonneg n])
    · rw [min_eq_right (le_of_not_ge hcase)]
      apply (min_le_right _ _).trans
      apply (div_le_iff hhp).mpr
      have hratio : A ≤ (81 / 4 : ℝ) * h := by linarith
      have hmult := mul_le_mul_of_nonneg_right hratio (pow_nonneg hn 4)
      have hgoal : N ^ 4 * A ≤ 3000 * n ^ 4 * h := by
        have hN4A := mul_le_mul_of_nonneg_right h4 (le_of_lt hAp)
        nlinarith only [hN4A, hmult,
          mul_nonneg (pow_nonneg hn 4) (le_of_lt hhp)]
      have hid : (3000 * (n ^ 4 / A) * h) * A = 3000 * n ^ 4 * h := by
        field_simp
      exact (mul_le_mul_right hAp).mp (by rw [hid]; exact hgoal)
  nlinarith only [hcompare, hlocal]

/-- The count budget after a half restriction has ample slack, including odd
original arities. All parameters are real here; integer rounding is upstream. -/
lemma half_restriction_count_budget (N n h M : ℝ)
    (hN : 0 ≤ N) (hn : 520 ≤ n) (hhalf : N ≤ 2 * n + 1)
    (hwidth : 1000 * h ≤ N ^ 3) (hcount : 4 * M ≤ h) :
    240 * M ≤ n * (n - 1) * (n - 2) := by
  have hdiff : 0 ≤ n - 520 := by linarith
  have hpoly : 0 ≤ 26 * (n - 520) ^ 3 + 40374 * (n - 520) ^ 2 +
      20897842 * (n - 520) + 3605556237 := by positivity
  have hbudget : 3 * (2 * n + 1) ^ 3 ≤ 50 * n * (n - 1) * (n - 2) := by
    nlinarith only [hpoly]
  have hN3 : N ^ 3 ≤ (2 * n + 1) ^ 3 := by gcongr
  nlinarith only [hN3, hbudget, hwidth, hcount]

/-- In the complementary large-first-width regime, the previously proved
linear second-width bound is already stronger than the desired tradeoff. -/
lemma linear_bound_absorbs_large_first_width (N h W : ℝ)
    (hN : 1040 ≤ N) (hwidth : N ^ 3 < 1000 * h)
    (hlinear : N ≤ 2 * W + 2) :
    (1 / 10000000000000000 : ℝ) * min (N ^ 2) (N ^ 4 / h) ≤ W := by
  have hNp : 0 < N := by linarith
  have hhp : 0 < h := by nlinarith only [hwidth, pow_pos hNp 3]
  have hratio : N ^ 4 / h ≤ 1000 * N := by
    apply (div_le_iff hhp).mpr
    have h := mul_le_mul_of_nonneg_left (le_of_lt hwidth) (le_of_lt hNp)
    nlinarith only [h]
  have hmin := (min_le_right (N ^ 2) (N ^ 4 / h)).trans hratio
  nlinarith only [hmin, hlinear, hN]

#check @counting_implies_moment_bound
#check @counting_implies_arity_tradeoff
#check @half_restriction_transfer
#check @half_restriction_count_budget
#check @linear_bound_absorbs_large_first_width
#print axioms counting_implies_moment_bound
#print axioms counting_implies_arity_tradeoff
#print axioms half_restriction_transfer
#print axioms half_restriction_count_budget
#print axioms linear_bound_absorbs_large_first_width
end MaxCaterpillar.WeightedTradeoff
