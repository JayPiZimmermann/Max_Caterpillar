import MaxCaterpillar.Frontier.RandomRestriction.GoodEventGeometry
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Run-length double counts and geometric expectation bounds

The only distributional input is an explicit finite-subset inclusion
estimate. `GoodEventSubset` proves that input for actual uniform ranks.
These lemmas count the actual path intervals and injective tail placements.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators

variable {m : ℕ} {Ω : Type*} [Fintype Ω]

noncomputable def containmentWeight (p : Ω → ℝ) (Γ : Ω → Finset (Fin m))
    (I : Finset (Fin m)) : ℝ := by
  classical
  exact ∑ ω, p ω * (if I ⊆ Γ ω then 1 else 0)

theorem geometric_sum_of_positive_injective {α : Type*} [DecidableEq α]
    (s : Finset α) (d : α → ℕ) (L : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hqone : q < 1)
    (hinj : Set.InjOn d s) (hdpos : ∀ i ∈ s, 0 < d i)
    (hdlt : ∀ i ∈ s, d i < L) :
    (∑ i in s, q ^ d i) ≤ q / (1 - q) := by
  classical
  have hsub : s.image d ⊆ Finset.Ico 1 L := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt (hdpos i hi), hdlt i hi⟩
  calc
    _ = ∑ n in s.image d, q ^ n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n in Finset.Ico 1 L, q ^ n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => pow_nonneg hq n)
    _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq hqone
    _ = q / (1 - q) := by rw [pow_one]

theorem upper_distance_sum_le (a : Fin m) (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1) :
    (∑ b in Finset.univ.filter (fun b : Fin m => a < b), q ^ (b.val - a.val)) ≤
      q / (1 - q) := by
  apply geometric_sum_of_positive_injective _ (fun b : Fin m => b.val - a.val) (m + 1)
    q hq hqone
  · intro b hb c hc hbc
    have hab : a.val ≤ b.val := (Finset.mem_filter.mp hb).2.le
    have hac : a.val ≤ c.val := (Finset.mem_filter.mp hc).2.le
    apply Fin.ext
    have hh := congrArg (fun n : ℕ => n + a.val) hbc
    simpa only [Nat.sub_add_cancel hab, Nat.sub_add_cancel hac] using hh
  · intro b hb
    exact Nat.sub_pos_of_lt (Finset.mem_filter.mp hb).2
  · intro b _
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_trans b.isLt (Nat.lt_succ_self m))

theorem successor_power_sum_le (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1) :
    (∑ a : Fin m, q ^ (a.val + 1)) ≤ q / (1 - q) := by
  apply geometric_sum_of_positive_injective Finset.univ (fun a : Fin m => a.val + 1)
    (m + 1) q hq hqone
  · intro a _ b _ hab
    apply Fin.ext
    exact Nat.add_right_cancel hab
  · intro a _
    exact Nat.succ_pos _
  · intro a _
    exact Nat.succ_lt_succ a.isLt

private theorem off_diagonal_symmetric_sum (f : Fin m → Fin m → ℝ)
    (hsym : ∀ a b, f a b = f b a) :
    (∑ a : Fin m, ∑ b : Fin m, if a ≠ b then f a b else 0) =
      2 * ∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0 := by
  have hpoint : ∀ a b,
      (if a ≠ b then f a b else 0) =
        (if a < b then f a b else 0) + (if b < a then f b a else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hba
    · simp [hab, ne_of_lt hab, not_lt_of_ge hab.le]
    · subst b
      simp
    · simp [hba, (ne_of_lt hba).symm, not_lt_of_ge hba.le, hsym a b]
  calc
    _ = (∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0) +
        ∑ a : Fin m, ∑ b : Fin m, if b < a then f b a else 0 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
    _ = (∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0) +
        ∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0 := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by ring

theorem orderedRunPairs_card_eq (Γ : Finset (Fin m)) :
    ((orderedRunPairs Γ).card : ℝ) =
      2 * ∑ a : Fin m, ∑ b in Finset.univ.filter (fun b : Fin m => a < b),
        if Finset.Ioc a b ⊆ Γ then (1 : ℝ) else 0 := by
  classical
  have hbase : ((orderedRunPairs Γ).card : ℝ) =
      ∑ a : Fin m, ∑ b : Fin m,
        if a ≠ b then (if TailSameRun Γ a b then (1 : ℝ) else 0) else 0 := by
    rw [orderedRunPairs, Finset.natCast_card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a ≠ b <;> by_cases hr : TailSameRun Γ a b <;> simp [hab, hr]
  rw [hbase, off_diagonal_symmetric_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a < b
    · simp [hab, TailSameRun, tailInterval, min_eq_left hab.le, max_eq_right hab.le]
    · simp [hab]
  · intro a b
    simp only [TailSameRun, tailInterval_comm a b]
    split_ifs <;> rfl

theorem weighted_anchor_count_eq (p : Ω → ℝ) (Γ : Ω → Finset (Fin m)) :
    (∑ ω, p ω * ((anchoredRun (Γ ω)).card : ℝ)) =
      ∑ a : Fin m, containmentWeight p Γ (Finset.Iic a) := by
  classical
  unfold anchoredRun
  simp only [Finset.natCast_card_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold containmentWeight AnchorSameRun
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : Finset.Iic a ⊆ Γ ω <;> simp only [h, if_pos, if_neg]

theorem weighted_ordered_run_count_eq (p : Ω → ℝ) (Γ : Ω → Finset (Fin m)) :
    (∑ ω, p ω * ((orderedRunPairs (Γ ω)).card : ℝ)) =
      2 * ∑ a : Fin m, ∑ b in Finset.univ.filter (fun b : Fin m => a < b),
        containmentWeight p Γ (Finset.Ioc a b) := by
  classical
  simp_rw [orderedRunPairs_card_eq]
  have hfactor : (∑ ω, p ω *
      (2 * ∑ a : Fin m, ∑ b in Finset.univ.filter (fun b : Fin m => a < b),
        if Finset.Ioc a b ⊆ Γ ω then (1 : ℝ) else 0)) =
      2 * ∑ ω, p ω *
        (∑ a : Fin m, ∑ b in Finset.univ.filter (fun b : Fin m => a < b),
          if Finset.Ioc a b ⊆ Γ ω then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [hfactor]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

/-- The anchor run expectation is controlled by a single geometric series. -/
theorem weighted_anchor_count_le (p : Ω → ℝ) (Γ : Ω → Finset (Fin m))
    (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1)
    (hI : ∀ I : Finset (Fin m), containmentWeight p Γ I ≤ q ^ I.card) :
    (∑ ω, p ω * ((anchoredRun (Γ ω)).card : ℝ)) ≤ q / (1 - q) := by
  rw [weighted_anchor_count_eq]
  calc
    _ ≤ ∑ a : Fin m, q ^ (a.val + 1) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [Fin.card_Iic] using hI (Finset.Iic a)
    _ ≤ _ := successor_power_sum_le q hq hqone

/-- Ordered distinct pairs in a common run cost at most twice m geometric
series. No independence between the adjacent-pair and run counts is used. -/
theorem weighted_ordered_run_count_le (p : Ω → ℝ) (Γ : Ω → Finset (Fin m))
    (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1)
    (hI : ∀ I : Finset (Fin m), containmentWeight p Γ I ≤ q ^ I.card) :
    (∑ ω, p ω * ((orderedRunPairs (Γ ω)).card : ℝ)) ≤
      2 * (m : ℝ) * q / (1 - q) := by
  classical
  rw [weighted_ordered_run_count_eq]
  calc
    _ ≤ 2 * ∑ a : Fin m, ∑ b in Finset.univ.filter (fun b : Fin m => a < b),
        q ^ (b.val - a.val) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simpa only [Fin.card_Ioc] using hI (Finset.Ioc a b)
    _ ≤ 2 * ∑ a : Fin m, q / (1 - q) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a _ => upper_distance_sum_le a q hq hqone
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_div_assoc, mul_assoc]

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
