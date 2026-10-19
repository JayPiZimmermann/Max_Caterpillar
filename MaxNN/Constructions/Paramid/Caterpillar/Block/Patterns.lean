import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing

/-! # The unique constant-prefix / constant-suffix split

These predicates depend on the vertex values alone. Consequently changing
cuts inside either constant interval preserves the splitting index.
-/

namespace MaxNN.Caterpillar

variable {r : ℕ} {α : Type*}

def SplitValues (w : Fin (r + 1) → α) (j : Fin r) : Prop :=
  w 0 ≠ w j.succ ∧ ∀ i, w i = if i < j.succ then w 0 else w j.succ

theorem SplitValues.unique {w : Fin (r + 1) → α} {j k : Fin r}
    (hj : SplitValues w j) (hk : SplitValues w k) : j = k := by
  rcases lt_trichotomy j k with hlt | he | hgt
  · have h := hk.2 j.succ
    rw [if_pos (Fin.succ_lt_succ_iff.mpr hlt)] at h
    exact False.elim (hj.1 h.symm)
  · exact he
  · have h := hj.2 k.succ
    rw [if_pos (Fin.succ_lt_succ_iff.mpr hgt)] at h
    exact False.elim (hk.1 h.symm)

theorem SplitValues.parent_eq {w : Fin (r + 1) → α} {j : Fin r}
    (h : SplitValues w j) {S : Finset (Fin (r + 1))} (hj : j.succ ∈ S)
    (k : Fin r) (hk : k ≠ j) : w k.succ = w (parent S k.succ) := by
  by_cases hlt : k.succ < j.succ
  · rw [h.2 k.succ, h.2 (parent S k.succ), if_pos hlt,
      if_pos (lt_trans (parent_lt (Fin.succ_pos k)) hlt)]
  · have hgt : j.succ < k.succ := lt_of_le_of_ne (not_lt.mp hlt)
      (fun he => hk (Fin.succ_injective r he.symm))
    have hp := le_parent_of_mem hj hgt
    rw [h.2 k.succ, h.2 (parent S k.succ), if_neg hlt, if_neg (not_lt.mpr hp)]

theorem SplitValues.crossing {w : Fin (r + 1) → α} {j : Fin r}
    (h : SplitValues w j) (S : Finset (Fin (r + 1))) :
    w j.succ ≠ w (parent S j.succ) := by
  rw [h.2 (parent S j.succ), if_pos (parent_lt (Fin.succ_pos j))]
  exact Ne.symm h.1

theorem SplitValues.prefix_has_two {w : Fin (r + 1) → α} {j : Fin r}
    (h : SplitValues w j) (hrep : ∃ i, i ≠ 0 ∧ w i = w 0) : 0 < j.castSucc := by
  obtain ⟨i, hi, hw⟩ := hrep
  have hlt : i < j.succ := by
    by_contra hn
    have he := h.2 i
    rw [if_neg hn, hw] at he
    exact h.1 he
  have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun he => hi (Fin.ext he))
  change i.val < j.val + 1 at hlt
  change 0 < j.val
  exact lt_of_lt_of_le hpos (Nat.lt_succ_iff.mp hlt)

theorem SplitValues.suffix_has_two {w : Fin (r + 1) → α} {j : Fin r}
    (h : SplitValues w j) (hrep : ∃ i, i ≠ j.succ ∧ w i = w j.succ) : j.succ.val < r := by
  obtain ⟨i, hi, hw⟩ := hrep
  have hge : j.succ ≤ i := by
    by_contra hn
    have he := h.2 i
    rw [if_pos (lt_of_not_ge hn), hw] at he
    exact h.1 he.symm
  have hgt : j.succ < i := lt_of_le_of_ne hge (Ne.symm hi)
  exact lt_of_lt_of_le hgt (Fin.le_last i)

end MaxNN.Caterpillar
