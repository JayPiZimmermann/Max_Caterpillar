import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Cancellation of interior knots in a finite scalar ReLU representation

The proof uses a common positive step and exact symmetric differences. It
requires neither differentiability nor a genericity condition on the affine
forms. Zero slopes, zero output weights, and coincident knots are included.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Connected64

open BigOperators

private theorem exists_positive_step {ι : Type*} (s : Finset ι) (a c : ι → ℝ)
    (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∀ i ∈ s, c i ≠ 0 → ε * |a i| ≤ |c i| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨r, hr, le_rfl, by simp⟩
  | @insert i s hi ih =>
    rcases ih with ⟨ε, hε, hεr, hεs⟩
    by_cases hc : c i = 0
    · exact ⟨ε, hε, hεr, by
        intro j hj hjc
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact False.elim (hjc hc)
        · exact hεs j hjs hjc⟩
    · let δ : ℝ := |c i| / (|a i| + 1)
      have hden : 0 < |a i| + 1 := by linarith [abs_nonneg (a i)]
      have hδ : 0 < δ := div_pos (abs_pos.mpr hc) hden
      have hδbound : δ * |a i| ≤ |c i| := by
        have hcancel : δ * (|a i| + 1) = |c i| :=
          div_mul_cancel _ (ne_of_gt hden)
        nlinarith
      refine ⟨min ε δ, lt_min hε hδ, (min_le_left _ _).trans hεr, ?_⟩
      intro j hj hjc
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)).trans hδbound
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans
          (hεs j hjs hjc)

/-- The exact symmetric difference of one ReLU, with the step small enough
that a nonzero central preactivation does not change sign. -/
theorem relu_symmetric_difference (a c ε : ℝ) (hε : 0 ≤ ε)
    (hc : c ≠ 0 → ε * |a| ≤ |c|) :
    max 0 (c + ε * a) + max 0 (c - ε * a) - 2 * max 0 c =
      if c = 0 then ε * |a| else 0 := by
  split_ifs with hz
  · subst c
    simp only [zero_add, zero_sub, max_self, mul_zero, sub_zero]
    have habs : max 0 (ε * a) + max 0 (-(ε * a)) = |ε * a| := by
      simpa only [max_comm] using max_zero_add_max_neg_zero_eq_abs_self (ε * a)
    rw [habs, abs_mul, abs_of_nonneg hε]
  · have hbound : |ε * a| ≤ |c| := by
      rw [abs_mul, abs_of_nonneg hε]
      exact hc hz
    rcases le_total 0 c with hp | hn
    · rw [abs_of_nonneg hp] at hbound
      have hplus : 0 ≤ c + ε * a := by linarith [(abs_le.mp hbound).1]
      have hminus : 0 ≤ c - ε * a := by linarith [(abs_le.mp hbound).2]
      rw [max_eq_right hplus, max_eq_right hminus, max_eq_right hp]
      ring
    · rw [abs_of_nonpos hn] at hbound
      have hplus : c + ε * a ≤ 0 := by linarith [(abs_le.mp hbound).2]
      have hminus : c - ε * a ≤ 0 := by linarith [(abs_le.mp hbound).1]
      rw [max_eq_left hplus, max_eq_left hminus, max_eq_left hn]
      ring

/-- Every strict interior knot has total weighted absolute-slope jump zero
when a finite sum of ReLUs is affine on the nonnegative half-line. -/
theorem interior_knot_jump_zero {ι : Type*} [Fintype ι]
    (a b d : ι → ℝ) (α β τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = α * x + β) :
    (∑ i in Finset.univ.filter (fun i => a i * τ + b i = 0), d i * |a i|) = 0 := by
  classical
  rcases exists_positive_step Finset.univ a (fun i => a i * τ + b i) τ hτ with
    ⟨ε, hε, hετ, hsmall⟩
  have hplus := hfit (τ + ε) (by linarith)
  have hminus := hfit (τ - ε) (sub_nonneg.mpr hετ)
  have hzero := hfit τ hτ.le
  have heach : ∀ i : ι,
      max 0 (a i * (τ + ε) + b i) + max 0 (a i * (τ - ε) + b i) -
        2 * max 0 (a i * τ + b i) =
        if a i * τ + b i = 0 then ε * |a i| else 0 := by
    intro i
    have h := relu_symmetric_difference (a i) (a i * τ + b i) ε hε.le
      (hsmall i (Finset.mem_univ i))
    have hp : a i * (τ + ε) + b i = (a i * τ + b i) + ε * a i := by ring
    have hm : a i * (τ - ε) + b i = (a i * τ + b i) - ε * a i := by ring
    rw [hp, hm]
    exact h
  have hdiff : (∑ i, d i * (max 0 (a i * (τ + ε) + b i) +
      max 0 (a i * (τ - ε) + b i) - 2 * max 0 (a i * τ + b i))) = 0 := by
    calc
      _ = (∑ i, d i * max 0 (a i * (τ + ε) + b i)) +
          (∑ i, d i * max 0 (a i * (τ - ε) + b i)) -
          2 * ∑ i, d i * max 0 (a i * τ + b i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = 0 := by rw [hplus, hminus, hzero]; ring
  have hjump : ε * (∑ i in Finset.univ.filter (fun i => a i * τ + b i = 0),
      d i * |a i|) = 0 := by
    rw [Finset.sum_filter, Finset.mul_sum]
    calc
      _ = ∑ i, d i * (if a i * τ + b i = 0 then ε * |a i| else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        split_ifs <;> ring
      _ = 0 := by simp_rw [← heach]; exact hdiff
  exact (mul_eq_zero.mp hjump).resolve_left (ne_of_gt hε)

/-- A nonzero weighted gate cannot be the only effective gate at an interior
knot of an affine sum. Its partner has nonzero slope and output weight. -/
theorem interior_knot_has_partner {ι : Type*} [Fintype ι]
    (a b d : ι → ℝ) (α β τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = α * x + β)
    (j : ι) (hj : a j * τ + b j = 0) (ha : a j ≠ 0) (hd : d j ≠ 0) :
    ∃ k : ι, k ≠ j ∧ a k * τ + b k = 0 ∧ d k ≠ 0 ∧ a k ≠ 0 := by
  classical
  by_contra hno
  have hother : ∀ k ∈ Finset.univ.filter (fun i => a i * τ + b i = 0),
      k ≠ j → d k * |a k| = 0 := by
    intro k hk hkj
    by_cases hdk : d k = 0
    · simp [hdk]
    by_cases hak : a k = 0
    · simp [hak]
    exact False.elim (hno ⟨k, hkj, (Finset.mem_filter.mp hk).2, hdk, hak⟩)
  have hsum : (∑ i in Finset.univ.filter (fun i => a i * τ + b i = 0),
      d i * |a i|) = d j * |a j| := by
    apply Finset.sum_eq_single j hother
    intro hnot
    exact False.elim (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
  have hz := interior_knot_jump_zero a b d α β τ hτ hfit
  rw [hsum] at hz
  exact (mul_ne_zero hd (ne_of_gt (abs_pos.mpr ha))) hz

/-- With at most three slots, all effective interior knots coincide. This is
the exhaustive knot-location reduction used in the quadrant argument. -/
theorem interior_knots_unique_of_card_le_three {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι ≤ 3) (a b d : ι → ℝ) (α β τ σ : ℝ)
    (hτ : 0 < τ) (hσ : 0 < σ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = α * x + β)
    (i j : ι) (hi : a i * τ + b i = 0) (hj : a j * σ + b j = 0)
    (hai : a i ≠ 0) (hdi : d i ≠ 0) (haj : a j ≠ 0) (hdj : d j ≠ 0) :
    τ = σ := by
  classical
  by_contra hne
  rcases interior_knot_has_partner a b d α β τ hτ hfit i hi hai hdi with
    ⟨k, hki, hk, _hdk, hak⟩
  rcases interior_knot_has_partner a b d α β σ hσ hfit j hj haj hdj with
    ⟨l, hlj, hl, _hdl, _hal⟩
  have separate : ∀ u v : ι, a u ≠ 0 → a u * τ + b u = 0 →
      a v * σ + b v = 0 → u ≠ v := by
    intro u v hau hu hv huv
    subst v
    have heq : a u * τ = a u * σ := by linarith
    exact hne (mul_left_cancel₀ hau heq)
  have hij := separate i j hai hi hj
  have hil := separate i l hai hi hl
  have hkj := separate k j hak hk hj
  have hkl := separate k l hak hk hl
  have hfour : ({i, k, j, l} : Finset ι).card = 4 := by
    simp [Ne.symm hki, hij, hil, hkj, hkl, Ne.symm hlj]
  have hbound : ({i, k, j, l} : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
  linarith

/-- If every gate vanishes at one interior point, an exact representation of
`x - 1` forces that common point to be `1`. -/
theorem common_knot_of_difference_target {ι : Type*} [Fintype ι]
    (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (hvanish : ∀ i, a i * τ + b i = 0) : τ = 1 := by
  have h := hfit τ hτ.le
  simp only [hvanish, max_self, mul_zero, Finset.sum_const_zero] at h
  linarith

/-- An affine form with no genuine knot in the strict positive half-line
has a single weak sign on the whole nonnegative quadrant after homogenizing. -/
theorem coefficients_same_sign_of_no_interior_knot (a b : ℝ)
    (h : ∀ τ : ℝ, 0 < τ → a ≠ 0 → a * τ + b ≠ 0) :
    (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  by_cases ha0 : a = 0
  · subst a
    rcases le_total 0 b with hb | hb
    · exact Or.inl ⟨le_rfl, hb⟩
    · exact Or.inr ⟨le_rfl, hb⟩
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · by_cases hb : b ≤ 0
    · exact Or.inr ⟨ha.le, hb⟩
    have hp : 0 < b / (-a) := div_pos (lt_of_not_ge hb) (neg_pos.mpr ha)
    have hz : a * (b / (-a)) + b = 0 := by
      have hc := div_mul_cancel b (neg_ne_zero.mpr ha0)
      nlinarith
    exact False.elim (h (b / (-a)) hp ha0 hz)
  · by_cases hb : 0 ≤ b
    · exact Or.inl ⟨ha.le, hb⟩
    have hp : 0 < (-b) / a := div_pos (neg_pos.mpr (lt_of_not_ge hb)) ha
    have hz : a * ((-b) / a) + b = 0 := by
      have hc := div_mul_cancel (-b) ha0
      nlinarith
    exact False.elim (h ((-b) / a) hp ha0 hz)

end MaxCaterpillar.Fiber.Connected64
