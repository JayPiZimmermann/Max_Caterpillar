import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Monotone.Basic
import Std.Tactic.Omega

/-! # Tops and bottoms alternate along a path

Abstract combinatorics for the cubic lower bound on `s_N`
(`research/sN/NOTE.md`, "Cubic claim C", step 3).

A path has vertices `0, 1, …, L` (consecutive vertices adjacent), and
`r : ℕ → β` ranks the vertices; it must separate consecutive vertices.
`pathUp L r l ∈ {0, 1, 2}` is the number of path neighbours of `l` strictly
above `l`.  It is `0` exactly at local tops (all path neighbours below), `2`
exactly at interior local bottoms, and `1` at an interior vertex exactly when
the path is monotone through it.  Between two tops there is a bottom, between
two bottoms a top; a segment whose interior vertices all have `pathUp = 1` is
strictly monotone and contains at most one top.
-/

open Finset

namespace MaxCaterpillar.CountCubic

variable {β : Type*} [LinearOrder β]

/-- Number of path neighbours of `l` (on the path `0, …, L`) above `l`. -/
def pathUp (L : ℕ) (r : ℕ → β) (l : ℕ) : ℕ :=
  (if 0 < l ∧ r l < r (l - 1) then 1 else 0) + (if l < L ∧ r l < r (l + 1) then 1 else 0)

/-- `r` separates consecutive vertices of the path `0, …, L`. -/
def PathSep (L : ℕ) (r : ℕ → β) : Prop := ∀ i, i < L → r i ≠ r (i + 1)

variable {L : ℕ} {r : ℕ → β}

theorem pathUp_le_two (l : ℕ) : pathUp L r l ≤ 2 := by
  unfold pathUp; split_ifs <;> omega

/-- `pathUp = 0` exactly at local tops. -/
theorem pathUp_eq_zero_iff (hr : PathSep L r) (l : ℕ) (hl : l ≤ L) :
    pathUp L r l = 0 ↔ (0 < l → r (l - 1) < r l) ∧ (l < L → r (l + 1) < r l) := by
  unfold pathUp
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun hL => ?_⟩
    · have hne := hr (l - 1) (by omega)
      rw [show l - 1 + 1 = l by omega] at hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · exact h1
      · rw [if_pos ⟨h0, h1⟩] at h; omega
    · rcases lt_or_gt_of_ne (hr l hL) with h1 | h1
      · rw [if_pos (show l < L ∧ r l < r (l + 1) from ⟨hL, h1⟩)] at h; omega
      · exact h1
  · rintro ⟨h1, h2⟩
    rw [if_neg, if_neg]
    · rintro ⟨hL, h⟩; exact absurd (h2 hL) (not_lt.mpr h.le)
    · rintro ⟨h0, h⟩; exact absurd (h1 h0) (not_lt.mpr h.le)

/-- `pathUp = 2` exactly at interior local bottoms. -/
theorem pathUp_eq_two_iff (l : ℕ) :
    pathUp L r l = 2 ↔ 0 < l ∧ l < L ∧ r l < r (l - 1) ∧ r l < r (l + 1) := by
  unfold pathUp
  constructor
  · intro h
    split_ifs at h with h1 h2 <;> first | omega | exact ⟨h1.1, h2.1, h1.2, h2.2⟩
  · rintro ⟨h0, hL, h1, h2⟩
    rw [if_pos ⟨h0, h1⟩, if_pos ⟨hL, h2⟩]

/-- At an interior vertex, `pathUp = 1` exactly when the path is monotone
through it. -/
theorem pathUp_eq_one_iff (hr : PathSep L r) (l : ℕ) (h0 : 0 < l) (hL : l < L) :
    pathUp L r l = 1 ↔
      (r (l - 1) < r l ∧ r l < r (l + 1)) ∨ (r (l + 1) < r l ∧ r l < r (l - 1)) := by
  have hne := hr (l - 1) (by omega)
  rw [show l - 1 + 1 = l by omega] at hne
  have hne' := hr l hL
  unfold pathUp
  rcases lt_or_gt_of_ne hne with h1 | h1 <;> rcases lt_or_gt_of_ne hne' with h2 | h2
  · rw [if_neg (fun h => absurd h.2 (not_lt.mpr h1.le)), if_pos ⟨hL, h2⟩]
    exact iff_of_true rfl (Or.inl ⟨h1, h2⟩)
  · rw [if_neg (fun h => absurd h.2 (not_lt.mpr h1.le)),
      if_neg (fun h => absurd h.2 (not_lt.mpr h2.le))]
    refine iff_of_false (by decide) ?_
    rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact absurd h (not_lt.mpr h2.le)
    · exact absurd h (not_lt.mpr h1.le)
  · rw [if_pos ⟨h0, h1⟩, if_pos ⟨hL, h2⟩]
    refine iff_of_false (by decide) ?_
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact absurd h (not_lt.mpr h1.le)
    · exact absurd h (not_lt.mpr h2.le)
  · rw [if_pos ⟨h0, h1⟩, if_neg (fun h => absurd h.2 (not_lt.mpr h2.le))]
    exact iff_of_true rfl (Or.inr ⟨h2, h1⟩)

/-- **Between two tops there is a bottom.** -/
theorem exists_bottom_between_tops (hr : PathSep L r) {i j : ℕ} (hij : i < j)
    (hjL : j ≤ L) (hi : pathUp L r i = 0) (hj : pathUp L r j = 0) :
    ∃ l, i < l ∧ l < j ∧ pathUp L r l = 2 := by
  have ti := (pathUp_eq_zero_iff hr i (by omega)).mp hi
  have tj := (pathUp_eq_zero_iff hr j hjL).mp hj
  obtain ⟨l, hl, hmin⟩ := exists_min_image (Icc i j) r ⟨i, by simp [hij.le]⟩
  rw [mem_Icc] at hl
  have hli : l ≠ i := by
    rintro rfl
    have := hmin (l + 1) (by rw [mem_Icc]; omega)
    exact absurd (ti.2 (by omega)) (not_lt.mpr this)
  have hlj : l ≠ j := by
    rintro rfl
    have := hmin (l - 1) (by rw [mem_Icc]; omega)
    exact absurd (tj.1 (by omega)) (not_lt.mpr this)
  have hli' : i < l := lt_of_le_of_ne hl.1 (Ne.symm hli)
  have hlj' : l < j := lt_of_le_of_ne hl.2 hlj
  refine ⟨l, by omega, by omega, (pathUp_eq_two_iff l).mpr ⟨by omega, by omega, ?_, ?_⟩⟩
  · have hne := hr (l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at hne
    exact lt_of_le_of_ne (hmin (l - 1) (by rw [mem_Icc]; omega)) (Ne.symm hne)
  · exact lt_of_le_of_ne (hmin (l + 1) (by rw [mem_Icc]; omega)) (hr l (by omega))

/-- **Between two bottoms there is a top.** -/
theorem exists_top_between_bottoms (hr : PathSep L r) {i j : ℕ} (hij : i < j)
    (hi : pathUp L r i = 2) (hj : pathUp L r j = 2) :
    ∃ l, i < l ∧ l < j ∧ pathUp L r l = 0 := by
  have bi := (pathUp_eq_two_iff i).mp hi
  have bj := (pathUp_eq_two_iff j).mp hj
  obtain ⟨l, hl, hmax⟩ := exists_max_image (Icc i j) r ⟨i, by simp [hij.le]⟩
  rw [mem_Icc] at hl
  have hli : l ≠ i := by
    rintro rfl
    have := hmax (l + 1) (by rw [mem_Icc]; omega)
    exact absurd bi.2.2.2 (not_lt.mpr this)
  have hlj : l ≠ j := by
    rintro rfl
    have := hmax (l - 1) (by rw [mem_Icc]; omega)
    exact absurd bj.2.2.1 (not_lt.mpr this)
  have hli' : i < l := lt_of_le_of_ne hl.1 (Ne.symm hli)
  have hlj' : l < j := lt_of_le_of_ne hl.2 hlj
  refine ⟨l, by omega, by omega, (pathUp_eq_zero_iff hr l (by omega)).mpr ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · have hne := hr (l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at hne
    exact lt_of_le_of_ne (hmax (l - 1) (by rw [mem_Icc]; omega)) hne
  · exact lt_of_le_of_ne (hmax (l + 1) (by rw [mem_Icc]; omega)) (Ne.symm (hr l (by omega)))

theorem strictMonoOn_Icc_of_steps {i j : ℕ}
    (h : ∀ m, i ≤ m → m < j → r m < r (m + 1)) : StrictMonoOn r (Set.Icc i j) := by
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  induction b, hab using Nat.le_induction with
  | base => exact h a ha.1 (by omega)
  | succ b hab ih => exact lt_trans (ih ⟨by omega, by omega⟩) (h b (by omega) (by omega))

theorem strictAntiOn_Icc_of_steps {i j : ℕ}
    (h : ∀ m, i ≤ m → m < j → r (m + 1) < r m) : StrictAntiOn r (Set.Icc i j) := by
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  induction b, hab using Nat.le_induction with
  | base => exact h a ha.1 (by omega)
  | succ b hab ih => exact lt_trans (h b (by omega) (by omega)) (ih ⟨by omega, by omega⟩)

/-- **Runs are monotone.** If every interior vertex of the segment `[i, j]`
has exactly one path neighbour above it, `r` is strictly monotone on `[i, j]`. -/
theorem monotone_of_run (hr : PathSep L r) {i j : ℕ} (hjL : j ≤ L)
    (hrun : ∀ l, i < l → l < j → pathUp L r l = 1) :
    StrictMonoOn r (Set.Icc i j) ∨ StrictAntiOn r (Set.Icc i j) := by
  -- the direction of each step equals the direction of the first one
  have hdir : ∀ m, i ≤ m → m < j → (r m < r (m + 1) ↔ r i < r (i + 1)) := by
    intro m him hmj
    induction m, him using Nat.le_induction with
    | base => exact Iff.rfl
    | succ m him ih =>
      rw [← ih (by omega)]
      have h1 := (pathUp_eq_one_iff hr (m + 1) (by omega) (by omega)).mp
        (hrun (m + 1) (by omega) hmj)
      simp only [Nat.add_sub_cancel] at h1
      constructor
      · intro h; rcases h1 with h1 | h1
        · exact h1.1
        · exact absurd h (not_lt.mpr h1.1.le)
      · intro h; rcases h1 with h1 | h1
        · exact h1.2
        · exact absurd h (not_lt.mpr h1.2.le)
  rcases Nat.lt_or_ge i j with hij | hij
  · rcases lt_or_gt_of_ne (hr i (by omega)) with h | h
    · left
      exact strictMonoOn_Icc_of_steps fun m him hmj => (hdir m him hmj).mpr h
    · right
      refine strictAntiOn_Icc_of_steps fun m him hmj => ?_
      rcases lt_or_gt_of_ne (hr m (by omega)) with h' | h'
      · exact absurd ((hdir m him hmj).mp h') (not_lt.mpr h.le)
      · exact h'
  · left
    intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    omega

/-- **A run contains at most one top.** In a segment `[i, j]` whose interior
vertices all have `pathUp = 1`, two tops coincide. -/
theorem top_unique_of_run (hr : PathSep L r) {i j : ℕ} (hjL : j ≤ L)
    (hrun : ∀ l, i < l → l < j → pathUp L r l = 1) {a b : ℕ}
    (ha : a ∈ Set.Icc i j) (hb : b ∈ Set.Icc i j)
    (hta : pathUp L r a = 0) (htb : pathUp L r b = 0) : a = b := by
  simp only [Set.mem_Icc] at ha hb
  by_contra hab
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · obtain ⟨l, h1, h2, h3⟩ := exists_bottom_between_tops hr h (by omega) hta htb
    have := hrun l (by omega) (by omega)
    omega
  · obtain ⟨l, h1, h2, h3⟩ := exists_bottom_between_tops hr h (by omega) htb hta
    have := hrun l (by omega) (by omega)
    omega

end MaxCaterpillar.CountCubic
