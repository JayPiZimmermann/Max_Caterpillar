import MaxCaterpillar.Fiber.Connected64.Knots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.IntervalCases

/-! # The effective crossing gates of a three-slot quadrant representation

These are the algebraic classification steps, before constructing coefficient
paths. The fit condition is equality on the whole nonnegative half-line.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Connected64

open BigOperators

theorem crossing_iff_positive_knot (a b : ℝ) :
    a * b < 0 ↔ ∃ τ : ℝ, 0 < τ ∧ a ≠ 0 ∧ a * τ + b = 0 := by
  constructor
  · intro hab
    rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine ⟨(-b) / a, div_pos (neg_pos.mpr hb) ha, ne_of_gt ha, ?_⟩
      have hc := div_mul_cancel (-b) (ne_of_gt ha)
      nlinarith
    · refine ⟨b / (-a), div_pos hb (neg_pos.mpr ha), ne_of_lt ha, ?_⟩
      have hc := div_mul_cancel b (neg_ne_zero.mpr (ne_of_lt ha))
      nlinarith
  · rintro ⟨τ, hτ, ha, hz⟩
    have hs : 0 < a * a := mul_self_pos.mpr ha
    have hp : 0 < (a * a) * τ := mul_pos hs hτ
    have hb : b = -(a * τ) := by linarith
    rw [hb]
    nlinarith

/-- A gate is effective and crossing precisely when its output weight is
nonzero and the two homogenized coefficients have opposite signs. -/
noncomputable def crossingIndices (a b d : Fin 3 → ℝ) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => d i ≠ 0 ∧ a i * b i < 0)

theorem crossing_count_zero_two_or_three (a b d : Fin 3 → ℝ) (α β : ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = α * x + β) :
    (crossingIndices a b d).card = 0 ∨ (crossingIndices a b d).card = 2 ∨
      (crossingIndices a b d).card = 3 := by
  classical
  have hnotone : (crossingIndices a b d).card ≠ 1 := by
    intro hone
    rcases Finset.card_eq_one.mp hone with ⟨i, hi⟩
    have himem : i ∈ crossingIndices a b d := by rw [hi]; simp
    rcases (Finset.mem_filter.mp himem).2 with ⟨hdi, habi⟩
    rcases (crossing_iff_positive_knot (a i) (b i)).mp habi with ⟨τ, hτ, hai, hz⟩
    rcases interior_knot_has_partner a b d α β τ hτ hfit i hz hai hdi with
      ⟨j, hji, hj, hdj, haj⟩
    have hjmem : j ∈ crossingIndices a b d :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hdj,
        (crossing_iff_positive_knot (a j) (b j)).mpr ⟨τ, hτ, haj, hj⟩⟩
    rw [hi, Finset.mem_singleton] at hjmem
    exact hji hjmem
  have hbound : (crossingIndices a b d).card ≤ 3 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (crossingIndices a b d)
  interval_cases hcount : (crossingIndices a b d).card <;> simp_all

/-- With no effective crossing gate, each gate is unused or has a fixed weak
sign on the nonnegative quadrant. -/
theorem no_crossing_normal_form (a b d : Fin 3 → ℝ)
    (hzero : (crossingIndices a b d).card = 0) :
    ∀ i, d i = 0 ∨ (0 ≤ a i ∧ 0 ≤ b i) ∨ (a i ≤ 0 ∧ b i ≤ 0) := by
  classical
  intro i
  by_cases hd : d i = 0
  · exact Or.inl hd
  right
  apply coefficients_same_sign_of_no_interior_knot
  intro τ hτ ha hz
  have hab := (crossing_iff_positive_knot (a i) (b i)).mpr ⟨τ, hτ, ha, hz⟩
  have hi : i ∈ crossingIndices a b d :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hd, hab⟩
  have hempty := Finset.card_eq_zero.mp hzero
  rw [hempty] at hi
  exact Finset.not_mem_empty i hi

/-- In the no-crossing case the active linear forms have exactly the target's
two coefficients after the inactive forms have been discarded. -/
theorem no_crossing_group_weights (a b d : Fin 3 → ℝ)
    (hzero : (crossingIndices a b d).card = 0)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1) :
    (∑ i, d i * max 0 (a i)) = 1 ∧ (∑ i, d i * max 0 (b i)) = -1 := by
  have hforms := no_crossing_normal_form a b d hzero
  have hb := hfit 0 le_rfl
  simp only [mul_zero, zero_add, zero_sub] at hb
  have ha := hfit 1 (by norm_num)
  have hterm : ∀ i, d i * max 0 (a i * 1 + b i) =
      d i * max 0 (a i) + d i * max 0 (b i) := by
    intro i
    rcases hforms i with hd | ⟨hai, hbi⟩ | ⟨hai, hbi⟩
    · simp [hd]
    · rw [mul_one, max_eq_right (add_nonneg hai hbi), max_eq_right hai, max_eq_right hbi]
      ring
    · rw [mul_one, max_eq_left (add_nonpos hai hbi), max_eq_left hai, max_eq_left hbi]
      ring
  simp_rw [hterm] at ha
  rw [Finset.sum_add_distrib] at ha
  exact ⟨by linarith, hb⟩

/-- Both output signs occur on nonzero nonnegative forms in the no-crossing
case. Thus each sign group can be merged into one slot without losing a sign. -/
theorem no_crossing_active_signs (a b d : Fin 3 → ℝ)
    (hzero : (crossingIndices a b d).card = 0)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1) :
    (∃ i, 0 < d i ∧ 0 < a i ∧ 0 ≤ b i) ∧
      (∃ j, d j < 0 ∧ 0 ≤ a j ∧ 0 < b j) := by
  classical
  rcases no_crossing_group_weights a b d hzero hfit with ⟨hA, hB⟩
  have hforms := no_crossing_normal_form a b d hzero
  have hexpos : ∃ i, 0 < d i * max 0 (a i) := by
    by_contra hn
    have hall : ∀ i, d i * max 0 (a i) ≤ 0 :=
      fun i => le_of_not_gt (fun hi => hn ⟨i, hi⟩)
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun i _hi => hall i)
    linarith
  have hexneg : ∃ i, d i * max 0 (b i) < 0 := by
    by_contra hn
    have hall : ∀ i, 0 ≤ d i * max 0 (b i) :=
      fun i => le_of_not_gt (fun hi => hn ⟨i, hi⟩)
    have hs := Finset.sum_nonneg (s := Finset.univ) (fun i _hi => hall i)
    linarith
  constructor
  · rcases hexpos with ⟨i, hi⟩
    have hdi : 0 < d i := by
      by_contra hd
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) (le_max_left 0 (a i))
      linarith
    have hai : 0 < a i := by
      by_contra ha
      rw [max_eq_left (le_of_not_gt ha), mul_zero] at hi
      exact (lt_irrefl 0) hi
    refine ⟨i, hdi, hai, ?_⟩
    rcases hforms i with hd | ⟨_ha, hb⟩ | ⟨ha, _hb⟩
    · exact False.elim ((ne_of_gt hdi) hd)
    · exact hb
    · linarith
  · rcases hexneg with ⟨i, hi⟩
    have hdi : d i < 0 := by
      by_contra hd
      have hp := mul_nonneg (le_of_not_gt hd) (le_max_left 0 (b i))
      linarith
    have hbi : 0 < b i := by
      by_contra hb
      rw [max_eq_left (le_of_not_gt hb), mul_zero] at hi
      exact (lt_irrefl 0) hi
    refine ⟨i, hdi, ?_, hbi⟩
    rcases hforms i with hd | ⟨ha, _hb⟩ | ⟨_ha, hb⟩
    · exact False.elim ((ne_of_lt hdi) hd)
    · exact ha
    · linarith

/-- When all three gates cross, every preactivation is proportional to
`x - 1`. All coefficients and output weights remain arbitrary real numbers. -/
theorem all_three_crossing_normal_form (a b d : Fin 3 → ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (hcross : ∀ i, d i ≠ 0 ∧ a i * b i < 0) :
    ∀ i, b i = -(a i) := by
  rcases (crossing_iff_positive_knot (a 0) (b 0)).mp (hcross 0).2 with
    ⟨τ, hτ, ha0, hz0⟩
  have hfit' : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = 1 * x + (-1) := by
    intro x hx
    simpa only [one_mul, sub_eq_add_neg] using hfit x hx
  have hall : ∀ i, a i * τ + b i = 0 := by
    intro i
    rcases (crossing_iff_positive_knot (a i) (b i)).mp (hcross i).2 with
      ⟨σ, hσ, hai, hzi⟩
    have heq := interior_knots_unique_of_card_le_three (by norm_num : Fintype.card (Fin 3) ≤ 3)
      a b d 1 (-1) τ σ hτ hσ hfit' 0 i hz0 hzi ha0 (hcross 0).1 hai (hcross i).1
    simpa only [← heq] using hzi
  have ht := common_knot_of_difference_target a b d τ hτ hfit hall
  intro i
  have hi := hall i
  rw [ht, mul_one] at hi
  linarith

/-- The positive and negative orientation groups in the three-crossing case
have total normalized output coefficients `1` and `-1`. -/
theorem all_three_crossing_group_weights (a b d : Fin 3 → ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (hcross : ∀ i, d i ≠ 0 ∧ a i * b i < 0) :
    (∑ i, d i * max 0 (a i)) = 1 ∧ (∑ i, d i * max 0 (-(a i))) = -1 := by
  have hn := all_three_crossing_normal_form a b d hfit hcross
  have htwo := hfit 2 (by norm_num)
  have hzero := hfit 0 le_rfl
  have heval : ∀ i, a i * 2 + b i = a i := by
    intro i
    rw [hn i]
    ring
  simp only [heval] at htwo
  simp only [mul_zero, zero_add, hn, zero_sub] at hzero
  exact ⟨by linarith, hzero⟩

private theorem positive_part_mul (c u : ℝ) (hc : 0 ≤ c) :
    max 0 (c * u) = c * max 0 u := by
  rw [mul_max_of_nonneg 0 u hc, mul_zero]

/-- A pair of equally oriented knots with cancelling jumps cancels as a
function on the entire real line, not just near the knot. -/
theorem aligned_knot_pair_cancels (a₀ b₀ d₀ a₁ b₁ d₁ τ : ℝ)
    (hz₀ : a₀ * τ + b₀ = 0) (hz₁ : a₁ * τ + b₁ = 0)
    (hsame : (0 ≤ a₀ ∧ 0 ≤ a₁) ∨ (a₀ ≤ 0 ∧ a₁ ≤ 0))
    (hjump : d₀ * |a₀| + d₁ * |a₁| = 0) :
    ∀ x : ℝ, d₀ * max 0 (a₀ * x + b₀) + d₁ * max 0 (a₁ * x + b₁) = 0 := by
  intro x
  rcases hsame with ⟨ha₀, ha₁⟩ | ⟨ha₀, ha₁⟩
  · have h₀ : a₀ * x + b₀ = a₀ * (x - τ) := by nlinarith
    have h₁ : a₁ * x + b₁ = a₁ * (x - τ) := by nlinarith
    rw [h₀, h₁, positive_part_mul _ _ ha₀, positive_part_mul _ _ ha₁]
    rw [abs_of_nonneg ha₀, abs_of_nonneg ha₁] at hjump
    calc
      _ = (d₀ * a₀ + d₁ * a₁) * max 0 (x - τ) := by ring
      _ = 0 := by rw [hjump, zero_mul]
  · have h₀ : a₀ * x + b₀ = (-a₀) * (τ - x) := by nlinarith
    have h₁ : a₁ * x + b₁ = (-a₁) * (τ - x) := by nlinarith
    rw [h₀, h₁, positive_part_mul _ _ (neg_nonneg.mpr ha₀),
      positive_part_mul _ _ (neg_nonneg.mpr ha₁)]
    rw [abs_of_nonpos ha₀, abs_of_nonpos ha₁] at hjump
    calc
      _ = (d₀ * (-a₀) + d₁ * (-a₁)) * max 0 (τ - x) := by ring
      _ = 0 := by rw [hjump, zero_mul]

/-- A single weighted ReLU cannot represent the sign-changing affine target
on the nonnegative half-line. No sign restrictions on its parameters are used. -/
theorem not_one_gate_difference (a b d : ℝ) :
    ¬ ∀ x : ℝ, 0 ≤ x → d * max 0 (a * x + b) = x - 1 := by
  intro h
  rcases le_total 0 d with hd | hd
  · have hzero := h 0 le_rfl
    have hnonneg := mul_nonneg hd (le_max_left 0 (a * 0 + b))
    linarith
  · have htwo := h 2 (by norm_num)
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg hd (le_max_left 0 (a * 2 + b))
    linarith

/-- Exactly two effective crossing gates share one positive knot and their
weighted absolute slopes cancel there. -/
theorem two_crossing_common_knot (a b d : Fin 3 → ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (h₀ : d 0 ≠ 0 ∧ a 0 * b 0 < 0) (h₁ : d 1 ≠ 0 ∧ a 1 * b 1 < 0)
    (h₂ : d 2 = 0 ∨ 0 ≤ a 2 * b 2) :
    ∃ τ : ℝ, 0 < τ ∧ a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ a 0 * τ + b 0 = 0 ∧
      a 1 * τ + b 1 = 0 ∧ d 0 * |a 0| + d 1 * |a 1| = 0 := by
  classical
  rcases (crossing_iff_positive_knot (a 0) (b 0)).mp h₀.2 with ⟨τ, hτ, ha₀, hz₀⟩
  rcases (crossing_iff_positive_knot (a 1) (b 1)).mp h₁.2 with ⟨σ, hσ, ha₁, hz₁⟩
  have hfit' : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = 1 * x + (-1) := by
    intro x hx
    simpa only [one_mul, sub_eq_add_neg] using hfit x hx
  have heq := interior_knots_unique_of_card_le_three (by norm_num : Fintype.card (Fin 3) ≤ 3)
    a b d 1 (-1) τ σ hτ hσ hfit' 0 1 hz₀ hz₁ ha₀ h₀.1 ha₁ h₁.1
  have hz₁' : a 1 * τ + b 1 = 0 := by simpa only [heq] using hz₁
  have hthird : (if a 2 * τ + b 2 = 0 then d 2 * |a 2| else 0) = 0 := by
    rcases h₂ with hd | hab
    · simp [hd]
    split_ifs with hz
    · by_cases ha : a 2 = 0
      · simp [ha]
      have hneg := (crossing_iff_positive_knot (a 2) (b 2)).mpr ⟨τ, hτ, ha, hz⟩
      linarith
    · rfl
  have hjump := interior_knot_jump_zero a b d 1 (-1) τ hτ hfit'
  rw [Finset.sum_filter, Fin.sum_univ_three] at hjump
  simp only [hz₀, hz₁', if_pos, hthird, add_zero] at hjump
  exact ⟨τ, hτ, ha₀, ha₁, hz₀, hz₁', hjump⟩

/-- Exactly two effective interior-knot gates have opposite slope signs.
The third slot may have zero output weight or any noncrossing preactivation. -/
theorem two_crossing_opposite_slopes (a b d : Fin 3 → ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (h₀ : d 0 ≠ 0 ∧ a 0 * b 0 < 0) (h₁ : d 1 ≠ 0 ∧ a 1 * b 1 < 0)
    (h₂ : d 2 = 0 ∨ 0 ≤ a 2 * b 2) : a 0 * a 1 < 0 := by
  rcases two_crossing_common_knot a b d hfit h₀ h₁ h₂ with
    ⟨τ, _hτ, ha₀, _ha₁, hz₀, hz₁', hjump⟩
  by_contra hnot
  have hprod : 0 ≤ a 0 * a 1 := le_of_not_gt hnot
  have hsame : (0 ≤ a 0 ∧ 0 ≤ a 1) ∨ (a 0 ≤ 0 ∧ a 1 ≤ 0) := by
    rcases lt_or_gt_of_ne ha₀ with hn | hp
    · exact Or.inr ⟨hn.le, by nlinarith⟩
    · exact Or.inl ⟨hp.le, by nlinarith⟩
  have hcancel := aligned_knot_pair_cancels (a 0) (b 0) (d 0) (a 1) (b 1) (d 1)
    τ hz₀ hz₁' hsame hjump
  apply not_one_gate_difference (a 2) (b 2) (d 2)
  intro x hx
  have hf := hfit x hx
  rw [Fin.sum_univ_three] at hf
  linarith [hcancel x]

private theorem positive_negative_pair_linear (a₀ b₀ d₀ a₁ b₁ d₁ τ : ℝ)
    (ha₀ : 0 < a₀) (ha₁ : a₁ < 0)
    (hz₀ : a₀ * τ + b₀ = 0) (hz₁ : a₁ * τ + b₁ = 0)
    (hjump : d₀ * |a₀| + d₁ * |a₁| = 0) :
    ∀ x : ℝ, d₀ * max 0 (a₀ * x + b₀) + d₁ * max 0 (a₁ * x + b₁) =
      (d₀ * a₀) * (x - τ) := by
  intro x
  have h₀ : a₀ * x + b₀ = a₀ * (x - τ) := by nlinarith
  have h₁ : a₁ * x + b₁ = (-a₁) * (-(x - τ)) := by nlinarith
  rw [h₀, h₁, positive_part_mul _ _ ha₀.le, positive_part_mul _ _ (neg_nonneg.mpr ha₁.le)]
  rw [abs_of_nonneg ha₀.le, abs_of_nonpos ha₁.le] at hjump
  have hcoef : d₁ * (-a₁) = -(d₀ * a₀) := by linarith
  have hdiff : max 0 (x - τ) - max 0 (-(x - τ)) = x - τ := by
    simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self (x - τ)
  calc
    _ = (d₀ * a₀) * max 0 (x - τ) + (d₁ * (-a₁)) * max 0 (-(x - τ)) := by ring
    _ = (d₀ * a₀) * (max 0 (x - τ) - max 0 (-(x - τ))) := by rw [hcoef]; ring
    _ = (d₀ * a₀) * (x - τ) := by rw [hdiff]

/-- In the two-crossing case the first two slots jointly compute one nonzero
linear form. This identity is global in the scalar input. -/
theorem two_crossing_linear_pair (a b d : Fin 3 → ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (h₀ : d 0 ≠ 0 ∧ a 0 * b 0 < 0) (h₁ : d 1 ≠ 0 ∧ a 1 * b 1 < 0)
    (h₂ : d 2 = 0 ∨ 0 ≤ a 2 * b 2) :
    ∃ τ k : ℝ, 0 < τ ∧ k ≠ 0 ∧ ∀ x : ℝ,
      d 0 * max 0 (a 0 * x + b 0) + d 1 * max 0 (a 1 * x + b 1) = k * (x - τ) := by
  rcases two_crossing_common_knot a b d hfit h₀ h₁ h₂ with
    ⟨τ, hτ, ha₀, ha₁, hz₀, hz₁, hjump⟩
  have hopp := two_crossing_opposite_slopes a b d hfit h₀ h₁ h₂
  rcases mul_neg_iff.mp hopp with ⟨hp₀, hn₁⟩ | ⟨hn₀, hp₁⟩
  · exact ⟨τ, d 0 * a 0, hτ, mul_ne_zero h₀.1 ha₀,
      positive_negative_pair_linear _ _ _ _ _ _ _ hp₀ hn₁ hz₀ hz₁ hjump⟩
  · refine ⟨τ, d 1 * a 1, hτ, mul_ne_zero h₁.1 ha₁, ?_⟩
    intro x
    have hp := positive_negative_pair_linear (a 1) (b 1) (d 1) (a 0) (b 0) (d 0)
      τ hp₁ hn₀ hz₁ hz₀ (by linarith) x
    simpa only [add_comm] using hp

/-- Exact normal form of the two-crossing case: a nonzero linear signed-pair
contribution plus one nonnegative affine form with arbitrary output sign.
The equations are the coefficient identities needed by the contraction path. -/
theorem two_crossing_decomposition (a b d : Fin 3 → ℝ)
    (hfit : ∀ x : ℝ, 0 ≤ x →
      (∑ i, d i * max 0 (a i * x + b i)) = x - 1)
    (h₀ : d 0 ≠ 0 ∧ a 0 * b 0 < 0) (h₁ : d 1 ≠ 0 ∧ a 1 * b 1 < 0)
    (h₂ : d 2 = 0 ∨ 0 ≤ a 2 * b 2) :
    ∃ τ k p q e : ℝ, 0 < τ ∧ k ≠ 0 ∧ 0 ≤ p ∧ 0 ≤ q ∧
      (∀ x : ℝ, d 0 * max 0 (a 0 * x + b 0) + d 1 * max 0 (a 1 * x + b 1) =
        k * (x - τ)) ∧
      (∀ x : ℝ, 0 ≤ x → d 2 * max 0 (a 2 * x + b 2) = e * (p * x + q)) ∧
      k + e * p = 1 ∧ -k * τ + e * q = -1 := by
  rcases two_crossing_linear_pair a b d hfit h₀ h₁ h₂ with ⟨τ, k, hτ, hk, hpair⟩
  have hbase : ∃ p q e : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
      ∀ x : ℝ, 0 ≤ x → d 2 * max 0 (a 2 * x + b 2) = e * (p * x + q) := by
    rcases h₂ with hd | hab
    · exact ⟨0, 0, 0, le_rfl, le_rfl, by intro x _hx; simp [hd]⟩
    have hsign := coefficients_same_sign_of_no_interior_knot (a 2) (b 2)
      (fun s hs ha hz => by
        have hneg := (crossing_iff_positive_knot (a 2) (b 2)).mpr ⟨s, hs, ha, hz⟩
        linarith)
    rcases hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine ⟨a 2, b 2, d 2, ha, hb, ?_⟩
      intro x hx
      rw [max_eq_right (add_nonneg (mul_nonneg ha hx) hb)]
    · refine ⟨0, 0, 0, le_rfl, le_rfl, ?_⟩
      intro x hx
      rw [max_eq_left (add_nonpos (mul_nonpos_of_nonpos_of_nonneg ha hx) hb)]
      ring
  rcases hbase with ⟨p, q, e, hp, hq, hbase⟩
  refine ⟨τ, k, p, q, e, hτ, hk, hp, hq, hpair, hbase, ?_, ?_⟩
  all_goals
    have hz := hfit 0 le_rfl
    have ho := hfit 1 (by norm_num)
    rw [Fin.sum_univ_three, hpair, hbase _ le_rfl] at hz
    rw [Fin.sum_univ_three, hpair, hbase _ (by norm_num)] at ho
    nlinarith

end MaxCaterpillar.Fiber.Connected64
