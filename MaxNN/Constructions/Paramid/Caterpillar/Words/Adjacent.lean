import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing
import Mathlib.GroupTheory.Perm.Basic

/-! # Adjacent cut moves

Inserting a cut changes a parent to the maximum of its old value and the new
cut.  The specializations below isolate the one edge changed by adjacent cut
moves.  They are pointwise identities for arbitrary real vertex values.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ}

theorem parent_insert_eq_max (S : Finset (Fin (r + 1)))
    (c k : Fin (r + 1)) (hck : c < k) :
    parent (insert c S) k = max (parent S k) c := by
  apply le_antisymm
  · rcases Finset.mem_insert.mp (parent_mem_insert (insert c S) k) with h0 | hm
    · rw [h0]
      exact Fin.zero_le _
    · rcases Finset.mem_insert.mp hm with hc | hs
      · rw [hc]
        exact le_max_right _ _
      · exact le_trans (le_parent_of_mem hs (parent_lt (lt_of_le_of_lt (Fin.zero_le c) hck)))
          (le_max_left _ _)
  · apply max_le
    · rcases Finset.mem_insert.mp (parent_mem_insert S k) with h0 | hs
      · rw [h0]
        exact Fin.zero_le _
      · exact le_parent_of_mem (Finset.mem_insert_of_mem hs)
          (parent_lt (lt_of_le_of_lt (Fin.zero_le c) hck))
    · exact le_parent_of_mem (Finset.mem_insert_self _ _) hck

theorem parent_insert_eq_of_not_lt (S : Finset (Fin (r + 1)))
    (c k : Fin (r + 1)) (hck : ¬c < k) :
    parent (insert c S) k = parent S k := by
  unfold parent
  simp only [Finset.filter_insert, if_neg hck]

theorem lastHead_insert_eq_max (S : Finset (Fin (r + 1))) (c : Fin (r + 1)) :
    lastHead (insert c S) = max (lastHead S) c := by
  apply le_antisymm
  · have hm := Finset.max'_mem (insert 0 (insert c S)) (Finset.insert_nonempty _ _)
    change lastHead (insert c S) ∈ insert 0 (insert c S) at hm
    rcases Finset.mem_insert.mp hm with h0 | hm
    · rw [h0]
      exact Fin.zero_le _
    · rcases Finset.mem_insert.mp hm with hc | hs
      · rw [hc]
        exact le_max_right _ _
      · exact le_trans (Finset.le_max' _ _ (Finset.mem_insert_of_mem hs)) (le_max_left _ _)
  · apply max_le
    · apply Finset.max'_subset (Finset.insert_nonempty _ _)
      intro i hi
      rcases Finset.mem_insert.mp hi with h0 | hs
      · exact Finset.mem_insert.mpr (Or.inl h0)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hs)
    · exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

def adjacentSwap (j : Fin r) : Equiv.Perm (Fin (r + 1)) :=
  Equiv.swap j.castSucc j.succ

private theorem adjacent_lt (j : Fin r) : j.castSucc < j.succ := by
  exact Fin.castSucc_lt_succ j

private theorem le_castSucc_of_lt_succ {k : Fin (r + 1)} (j : Fin r)
    (hk : k < j.succ) : k ≤ j.castSucc := by
  change k.val ≤ j.val
  change k.val < j.val + 1 at hk
  omega

theorem parent_insert_left_at_right (S : Finset (Fin (r + 1))) (j : Fin r) :
    parent (insert j.castSucc S) j.succ = j.castSucc := by
  rw [parent_insert_eq_max S _ _ (adjacent_lt j), max_eq_right]
  exact le_castSucc_of_lt_succ j (parent_lt (Fin.succ_pos j))

theorem parent_insert_left_of_right_mem (S : Finset (Fin (r + 1))) (j : Fin r)
    (hb : j.succ ∈ S) (k : Fin (r + 1)) (hk : k ≠ j.succ) :
    parent (insert j.castSucc S) k = parent S k := by
  by_cases hak : j.castSucc < k
  · rw [parent_insert_eq_max S _ _ hak, max_eq_left]
    have hbk : j.succ < k := lt_of_le_of_ne
      (show j.succ ≤ k from by
        change j.val + 1 ≤ k.val
        change j.val < k.val at hak
        omega)
      (Ne.symm hk)
    exact le_trans (le_of_lt (adjacent_lt j)) (le_parent_of_mem (S := S) hb hbk)
  · exact parent_insert_eq_of_not_lt S _ _ hak

theorem lastHead_insert_left_of_right_mem (S : Finset (Fin (r + 1))) (j : Fin r)
    (hb : j.succ ∈ S) :
    lastHead (insert j.castSucc S) = lastHead S := by
  rw [lastHead_insert_eq_max, max_eq_left]
  exact le_trans (le_of_lt (adjacent_lt j))
    (Finset.le_max' _ _ (Finset.mem_insert_of_mem hb))

theorem treeMax_insert_left_of_right_mem (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hb : j.succ ∈ S) :
    treeMax w (insert j.castSucc S) - treeMax w S =
      max (w j.castSucc) (w j.succ) - max (w (parent S j.succ)) (w j.succ) := by
  unfold treeMax
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · rw [parent_insert_left_at_right]
  · intro k _ hkj
    rw [parent_insert_left_of_right_mem S j hb k.succ
      (fun he => hkj (Fin.succ_injective r he)), sub_self]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem baseMax_insert_left_of_right_mem (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hb : j.succ ∈ S) :
    baseMax w (insert j.castSucc S) - baseMax w S =
      max (w j.castSucc) (w j.succ) - max (w (parent S j.succ)) (w j.succ) := by
  unfold baseMax pointedMax
  rw [lastHead_insert_left_of_right_mem S j hb]
  have ht := treeMax_insert_left_of_right_mem w S j hb
  linarith

private theorem adjacentSwap_apply_left (j : Fin r) :
    adjacentSwap j j.castSucc = j.succ := by
  exact Equiv.swap_apply_left _ _

private theorem adjacentSwap_apply_right (j : Fin r) :
    adjacentSwap j j.succ = j.castSucc := by
  exact Equiv.swap_apply_right _ _

private theorem adjacentSwap_apply_of_ne (j : Fin r) (k : Fin (r + 1))
    (hka : k ≠ j.castSucc) (hkb : k ≠ j.succ) :
    adjacentSwap j k = k := by
  exact Equiv.swap_apply_of_ne_of_ne hka hkb

theorem adjacentSwap_zero (j : Fin r) (ha : (0 : Fin (r + 1)) < j.castSucc) :
    adjacentSwap j 0 = 0 := by
  apply adjacentSwap_apply_of_ne
  · exact ne_of_lt ha
  · exact ne_of_lt (lt_trans ha (adjacent_lt j))

theorem parent_right_of_left_mem (S : Finset (Fin (r + 1))) (j : Fin r)
    (haS : j.castSucc ∈ S) : parent S j.succ = j.castSucc := by
  apply le_antisymm
  · exact le_castSucc_of_lt_succ j (parent_lt (Fin.succ_pos j))
  · exact le_parent_of_mem haS (adjacent_lt j)

theorem adjacentSwap_parent_insert_right_at_left (S : Finset (Fin (r + 1)))
    (j : Fin r) (ha0 : (0 : Fin (r + 1)) < j.castSucc) :
    adjacentSwap j (parent (insert j.succ S) j.castSucc) = parent S j.castSucc := by
  have hba : ¬j.succ < j.castSucc := not_lt_of_ge (le_of_lt (adjacent_lt j))
  rw [parent_insert_eq_of_not_lt S _ _ hba]
  apply adjacentSwap_apply_of_ne
  · exact ne_of_lt (parent_lt ha0)
  · exact ne_of_lt (lt_trans
      (parent_lt ha0) (adjacent_lt j))

theorem adjacentSwap_parent_insert_right_at_right (S : Finset (Fin (r + 1)))
    (j : Fin r) (haS : j.castSucc ∈ S) :
    adjacentSwap j (parent (insert j.succ S) j.succ) = j.succ := by
  rw [parent_insert_eq_of_not_lt S _ _ (lt_irrefl _), parent_right_of_left_mem S j haS,
    adjacentSwap_apply_left]

theorem adjacentSwap_parent_insert_right_of_ne (S : Finset (Fin (r + 1)))
    (j : Fin r) (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (haS : j.castSucc ∈ S) (hbS : j.succ ∉ S)
    (k : Fin (r + 1)) (hka : k ≠ j.castSucc) (hkb : k ≠ j.succ) :
    adjacentSwap j (parent (insert j.succ S) k) = parent S k := by
  by_cases hbk : j.succ < k
  · rw [parent_insert_eq_max S _ _ hbk]
    by_cases hp : parent S k = j.castSucc
    · rw [hp, max_eq_right (le_of_lt (adjacent_lt j)), adjacentSwap_apply_right]
    · have hap : j.castSucc ≤ parent S k :=
        le_parent_of_mem haS (lt_trans (adjacent_lt j) hbk)
      have hbp : j.succ ≤ parent S k := by
        have hlt : j.castSucc < parent S k := lt_of_le_of_ne hap (Ne.symm hp)
        exact hlt
      rw [max_eq_left hbp]
      apply adjacentSwap_apply_of_ne j
      · exact hp
      · intro he
        have hm := parent_mem_insert S k
        rw [he] at hm
        rcases Finset.mem_insert.mp hm with h0 | hs
        · exact Fin.succ_ne_zero j h0
        · exact hbS hs
  · rw [parent_insert_eq_of_not_lt S _ _ hbk]
    have hkb' : k < j.succ := lt_of_le_of_ne (not_lt.mp hbk) hkb
    have hka' : k < j.castSucc :=
      lt_of_le_of_ne (le_castSucc_of_lt_succ j hkb') hka
    by_cases hk0 : k = 0
    · subst k
      have hp0 : parent S (0 : Fin (r + 1)) = 0 := by
        unfold parent
        simp
      rw [hp0, adjacentSwap_zero j ha0]
    · apply adjacentSwap_apply_of_ne
      · exact ne_of_lt (lt_trans (parent_lt (Fin.pos_iff_ne_zero.mpr hk0)) hka')
      · exact ne_of_lt (lt_trans
          (lt_trans (parent_lt (Fin.pos_iff_ne_zero.mpr hk0)) hka') (adjacent_lt j))

theorem adjacentSwap_lastHead_insert_right (S : Finset (Fin (r + 1)))
    (j : Fin r) (haS : j.castSucc ∈ S) (hbS : j.succ ∉ S) :
    adjacentSwap j (lastHead (insert j.succ S)) = lastHead S := by
  rw [lastHead_insert_eq_max]
  by_cases hp : lastHead S = j.castSucc
  · rw [hp, max_eq_right (le_of_lt (adjacent_lt j)), adjacentSwap_apply_right]
  · have hap : j.castSucc ≤ lastHead S :=
      Finset.le_max' _ _ (Finset.mem_insert_of_mem haS)
    have hbp : j.succ ≤ lastHead S := by
      have hlt : j.castSucc < lastHead S := lt_of_le_of_ne hap (Ne.symm hp)
      exact hlt
    rw [max_eq_left hbp]
    apply adjacentSwap_apply_of_ne j _ hp
    intro he
    have hm := Finset.max'_mem (insert 0 S) (Finset.insert_nonempty _ _)
    change lastHead S ∈ insert 0 S at hm
    rw [he] at hm
    rcases Finset.mem_insert.mp hm with h0 | hs
    · exact Fin.succ_ne_zero j h0
    · exact hbS hs

theorem edgeMax_adjacentSwap_insert_right (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (haS : j.castSucc ∈ S) (hbS : j.succ ∉ S) (k : Fin r)
    (hka : k.succ ≠ j.castSucc) :
    max (w (adjacentSwap j (parent (insert j.succ S) k.succ)))
        (w (adjacentSwap j k.succ)) =
      max (w (parent S k.succ)) (w k.succ) := by
  by_cases hkb : k.succ = j.succ
  · have hkj : k = j := Fin.succ_injective r hkb
    subst k
    rw [adjacentSwap_parent_insert_right_at_right S j haS,
      parent_right_of_left_mem S j haS, adjacentSwap_apply_right, max_comm]
  · rw [adjacentSwap_parent_insert_right_of_ne S j ha0 haS hbS k.succ hka hkb,
      adjacentSwap_apply_of_ne j k.succ hka hkb]

theorem treeMax_adjacentSwap_insert_right (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (haS : j.castSucc ∈ S) (hbS : j.succ ∉ S) :
    treeMax (fun i => w (adjacentSwap j i)) (insert j.succ S) - treeMax w S =
      max (w (parent S j.castSucc)) (w j.succ) -
        max (w (parent S j.castSucc)) (w j.castSucc) := by
  let p : Fin r := ⟨j.val - 1, by
    exact lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
  have hpa : p.succ = j.castSucc := by
    apply Fin.ext
    change (j.val - 1) + 1 = j.val
    exact Nat.sub_add_cancel (show 1 ≤ j.val by exact ha0)
  unfold treeMax
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single p]
  · rw [hpa]
    change max (w (adjacentSwap j (parent (insert j.succ S) j.castSucc)))
        (w (adjacentSwap j j.castSucc)) -
        max (w (parent S j.castSucc)) (w j.castSucc) = _
    rw [adjacentSwap_parent_insert_right_at_left S j ha0, adjacentSwap_apply_left]
  · intro k _ hkp
    have hka : k.succ ≠ j.castSucc := by
      intro he
      apply hkp
      apply Fin.succ_injective r
      exact he.trans hpa.symm
    rw [edgeMax_adjacentSwap_insert_right w S j ha0 haS hbS k hka, sub_self]
  · intro hp
    exact False.elim (hp (Finset.mem_univ p))

theorem baseMax_adjacentSwap_insert_right (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (haS : j.castSucc ∈ S) (hbS : j.succ ∉ S) :
    baseMax (fun i => w (adjacentSwap j i)) (insert j.succ S) - baseMax w S =
      max (w (parent S j.castSucc)) (w j.succ) -
        max (w (parent S j.castSucc)) (w j.castSucc) := by
  unfold baseMax pointedMax
  dsimp only
  rw [adjacentSwap_lastHead_insert_right S j haS hbS,
    Fintype.sum_equiv (adjacentSwap j) (fun i => w (adjacentSwap j i)) w (fun _ => rfl),
    adjacentSwap_zero j ha0]
  have ht := treeMax_adjacentSwap_insert_right w S j ha0 haS hbS
  linarith

end MaxNN.Caterpillar
