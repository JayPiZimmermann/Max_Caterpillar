import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # Breakpoint masses from an exact one-variable ReLU identity

The proof uses a symmetric finite difference on an interval containing no
other breakpoint. No differentiability or distributional machinery is needed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Star65

open BigOperators

/-- A finite family of thresholds has a positive isolating radius around any
given point. A requested positive upper bound on that radius is retained. -/
lemma exists_breakpoint_radius {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (p b : ℝ) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ b ∧ ∀ j ∈ s, t j ≠ p → ε ≤ |t j - p| := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨b, hb, le_rfl, by simp⟩
  | @insert j s hj ih =>
      rcases ih with ⟨ε, he, heb, hs⟩
      by_cases ht : t j = p
      · refine ⟨ε, he, heb, ?_⟩
        intro i hi hip
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact (hip ht).elim
        · exact hs i hi hip
      · have hd : 0 < |t j - p| := abs_pos.mpr (sub_ne_zero.mpr ht)
        refine ⟨min ε |t j - p|, lt_min he hd, (min_le_left _ _).trans heb, ?_⟩
        intro i hi hip
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hs i hi hip)

/-- The isolated symmetric difference of one hinge is its radius at its
own threshold and vanishes at every other threshold. -/
lemma hinge_second_difference (t p ε : ℝ) (he : 0 < ε)
    (hsep : t ≠ p → ε ≤ |t - p|) :
    max 0 (t - (p + ε)) + max 0 (t - (p - ε)) - 2 * max 0 (t - p) =
      if t = p then ε else 0 := by
  classical
  rcases lt_trichotomy t p with htp | htp | htp
  · have hne : t ≠ p := ne_of_lt htp
    have hs := hsep hne
    rw [abs_of_neg (sub_neg.mpr htp)] at hs
    rw [if_neg hne,
      max_eq_left (by linarith only [htp, he] : t - (p + ε) ≤ 0),
      max_eq_left (by linarith only [hs] : t - (p - ε) ≤ 0),
      max_eq_left (sub_nonpos.mpr htp.le)]
    ring
  · subst t
    rw [if_pos rfl,
      max_eq_left (by linarith only [he] : p - (p + ε) ≤ 0),
      max_eq_right (by linarith only [he] : 0 ≤ p - (p - ε)),
      sub_self, max_self]
    ring
  · have hne : t ≠ p := ne_of_gt htp
    have hs := hsep hne
    rw [abs_of_pos (sub_pos.mpr htp)] at hs
    rw [if_neg hne,
      max_eq_right (by linarith only [hs] : 0 ≤ t - (p + ε)),
      max_eq_right (by linarith only [htp, he] : 0 ≤ t - (p - ε)),
      max_eq_right (sub_nonneg.mpr htp.le)]
    ring

private lemma max_as_hinge (t w : ℝ) : max t w = w + max 0 (t - w) := by
  rcases le_total t w with h | h
  · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
    ring

/-- The same isolated symmetric-difference formula for a two-way maximum. -/
lemma max_second_difference (t p ε : ℝ) (he : 0 < ε)
    (hsep : t ≠ p → ε ≤ |t - p|) :
    max t (p + ε) + max t (p - ε) - 2 * max t p =
      if t = p then ε else 0 := by
  rw [max_as_hinge t (p + ε), max_as_hinge t (p - ε), max_as_hinge t p]
  have h := hinge_second_difference t p ε he hsep
  linarith only [h]

/-- Equality on the nonnegative half-line forces equality of every positive
breakpoint mass. Repeated thresholds and zero coefficients are allowed. -/
theorem breakpoint_mass_of_identity {ι : Type*} (s : Finset ι) (a t : ι → ℝ)
    (α β target p : ℝ) (hp : 0 < p)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + ∑ j in s, a j * max 0 (t j - w) = max target w) :
    (∑ j in s, if t j = p then a j else 0) = if target = p then 1 else 0 := by
  classical
  obtain ⟨δ, hd, hdp, hδ⟩ := exists_breakpoint_radius s t p p hp
  let ε : ℝ := if target = p then δ else min δ |target - p|
  have he : 0 < ε := by
    dsimp [ε]
    split_ifs with h
    · exact hd
    · exact lt_min hd (abs_pos.mpr (sub_ne_zero.mpr h))
  have heδ : ε ≤ δ := by
    dsimp [ε]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hep : ε ≤ p := heδ.trans hdp
  have het : target ≠ p → ε ≤ |target - p| := by
    intro h
    dsimp [ε]
    rw [if_neg h]
    exact min_le_right _ _
  have hm := hid (p - ε) (sub_nonneg.mpr hep)
  have hz := hid p hp.le
  have hp' := hid (p + ε) (by linarith only [hp, he])
  have htarget := max_second_difference target p ε he het
  have hsum :
      (∑ j in s, a j * max 0 (t j - (p + ε))) +
        (∑ j in s, a j * max 0 (t j - (p - ε))) -
        2 * (∑ j in s, a j * max 0 (t j - p)) =
      ε * (∑ j in s, if t j = p then a j else 0) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjdiff := hinge_second_difference (t j) p ε he
      (fun h => heδ.trans (hδ j hj h))
    calc
      _ = a j * (max 0 (t j - (p + ε)) + max 0 (t j - (p - ε)) -
          2 * max 0 (t j - p)) := by ring
      _ = a j * (if t j = p then ε else 0) := by rw [hjdiff]
      _ = _ := by split_ifs <;> ring
  have heq : ε * (∑ j in s, if t j = p then a j else 0) =
      if target = p then ε else 0 := by
    linarith only [hm, hz, hp', htarget, hsum]
  by_cases ht : target = p
  · rw [if_pos ht] at heq ⊢
    nlinarith only [he, heq]
  · rw [if_neg ht] at heq ⊢
    exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt he)

/-- A positive target breakpoint must be carried by at least one positive
output coefficient. Other coefficients may have either sign. -/
theorem exists_positive_carrier {ι : Type*} (s : Finset ι) (a t : ι → ℝ)
    (α β target : ℝ) (ht : 0 < target)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + ∑ j in s, a j * max 0 (t j - w) = max target w) :
    ∃ j ∈ s, t j = target ∧ 0 < a j := by
  classical
  have hm := breakpoint_mass_of_identity s a t α β target target ht hid
  rw [if_pos rfl] at hm
  by_contra hn
  have hnon : (∑ j in s, if t j = target then a j else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    by_cases he : t j = target
    · rw [if_pos he]
      exact le_of_not_gt (fun hp => hn ⟨j, hj, he, hp⟩)
    · rw [if_neg he]
  linarith only [hm, hnon]

/-- A positive coefficient at a spurious positive breakpoint needs a
negative coefficient at the identical breakpoint. -/
theorem exists_negative_canceling_carrier {ι : Type*} (s : Finset ι)
    (a t : ι → ℝ) (α β target : ℝ) (i : ι) (hi : i ∈ s)
    (hti : 0 < t i) (hai : 0 < a i) (hne : target ≠ t i)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + ∑ j in s, a j * max 0 (t j - w) = max target w) :
    ∃ j ∈ s, t j = t i ∧ a j < 0 := by
  classical
  have hm := breakpoint_mass_of_identity s a t α β target (t i) hti hid
  rw [if_neg hne] at hm
  by_contra hn
  have hnon : ∀ j ∈ s, 0 ≤ (if t j = t i then a j else 0) := by
    intro j hj
    by_cases he : t j = t i
    · rw [if_pos he]
      exact le_of_not_gt (fun hp => hn ⟨j, hj, he, hp⟩)
    · rw [if_neg he]
  have hle := Finset.single_le_sum hnon hi
  rw [if_pos rfl, hm] at hle
  linarith only [hai, hle]

/-- With one strictly negative output coefficient, one of the other two
thresholds must carry a positive target breakpoint. No sign assumption on
the first two coefficients is needed for this necessary condition. -/
theorem three_hinge_target_split (a b γ P Q N α β target : ℝ)
    (hg : 0 < γ) (ht : 0 < target)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + a * max 0 (P - w) + b * max 0 (Q - w) -
        γ * max 0 (N - w) = max target w) :
    P = target ∨ Q = target := by
  have hf : ∀ w : ℝ, 0 ≤ w →
      α * w + β + ∑ j : Fin 3, (![a, b, -γ] j) * max 0 (![P, Q, N] j - w) =
        max target w := by
    intro w hw
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hid w hw
  rcases exists_positive_carrier Finset.univ ![a, b, -γ] ![P, Q, N]
    α β target ht hf with ⟨j, _, hj, hjpos⟩
  fin_cases j
  · exact Or.inl hj
  · exact Or.inr hj
  · change 0 < -γ at hjpos
    linarith only [hg, hjpos]

/-- The two discrete alternatives in the normalized positive-path residual
classification follow already from the single feature state `U = V = 1`.
The remaining threshold and affine remainder are unrestricted. -/
theorem star_branch_split (a b γ h k n α β : ℝ) (hg : 0 < γ)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + a * max 0 (2 + h - w) + b * max 0 (1 + k - w) -
        γ * max 0 (n - w) = max 2 w) :
    h = 0 ∨ k = 1 := by
  have hsplit := three_hinge_target_split a b γ (2 + h) (1 + k) n α β 2 hg
    (by norm_num) hid
  rcases hsplit with hsplit | hsplit
  · exact Or.inl (by linarith only [hsplit])
  · exact Or.inr (by linarith only [hsplit])

end MaxCaterpillar.Fiber.Star65
