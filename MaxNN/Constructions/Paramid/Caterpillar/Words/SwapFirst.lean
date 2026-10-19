import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing
import Mathlib.GroupTheory.Perm.Basic

/-! # Swapping the first two vertices while toggling the first cut

This is the suffix counterpart of last-endpoint cancellation. The local
identity keeps the pointed base at the root fixed by swapping positions zero
and one and inserting the cut at one. It avoids reversing block lists.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ}

def firstSwap (r : ℕ) : Equiv.Perm (Fin (r + 1 + 1)) := Equiv.swap 0 1

private theorem firstSwap_max_one (i : Fin (r + 1 + 1)) (hi : i ≠ 1) :
    firstSwap r (max i 1) = i := by
  by_cases hz : i = 0
  · subst i
    rw [max_eq_right (show (0 : Fin (r + 1 + 1)) ≤ 1 from Fin.zero_le _)]
    exact Equiv.swap_apply_right _ _
  · have hle : (1 : Fin (r + 1 + 1)) ≤ i := by
      have hv : i.val ≠ 0 := fun he => hz (Fin.ext he)
      change 1 ≤ i.val
      exact Nat.one_le_iff_ne_zero.mpr hv
    rw [max_eq_left hle]
    exact Equiv.swap_apply_of_ne_of_ne hz hi

theorem parent_insert_one (S : Finset (Fin (r + 1 + 1)))
    (j : Fin (r + 1 + 1)) (hj : 1 < j) :
    parent (insert 1 S) j = max (parent S j) 1 := by
  have hj0 : 0 < j := lt_trans (Fin.succ_pos 0) hj
  apply le_antisymm
  · rcases Finset.mem_insert.mp (parent_mem_insert (insert 1 S) j) with hz | hm
    · rw [hz]
      exact Fin.zero_le _
    · rcases Finset.mem_insert.mp hm with he | hs
      · rw [he]
        exact le_max_right _ _
      · exact le_trans (le_parent_of_mem hs (parent_lt hj0)) (le_max_left _ _)
  · apply max_le
    · rcases Finset.mem_insert.mp (parent_mem_insert S j) with hz | hs
      · rw [hz]
        exact Fin.zero_le _
      · exact le_parent_of_mem (Finset.mem_insert_of_mem hs) (parent_lt hj0)
    · exact le_parent_of_mem (Finset.mem_insert_self _ _) hj

theorem parent_one (S : Finset (Fin (r + 1 + 1))) : parent S 1 = 0 := by
  have h := parent_lt (S := S) (show (0 : Fin (r + 1 + 1)) < 1 from Fin.succ_pos 0)
  apply Fin.ext
  change (parent S 1).val < 1 at h
  change (parent S 1).val = 0
  exact Nat.lt_one_iff.mp h

theorem firstSwap_parent_insert_one (S : Finset (Fin (r + 1 + 1)))
    (hS : (1 : Fin (r + 1 + 1)) ∉ S) (j : Fin (r + 1 + 1)) (hj : 1 < j) :
    firstSwap r (parent (insert 1 S) j) = parent S j := by
  rw [parent_insert_one S j hj]
  apply firstSwap_max_one
  intro he
  have hm := parent_mem_insert S j
  rw [he] at hm
  rcases Finset.mem_insert.mp hm with hz | hs
  · exact Fin.succ_ne_zero (0 : Fin (r + 1)) hz
  · exact hS hs

theorem firstSwap_lastHead_insert_one (S : Finset (Fin (r + 1 + 1)))
    (hS : (1 : Fin (r + 1 + 1)) ∉ S) :
    firstSwap r (lastHead (insert 1 S)) = lastHead S := by
  have he : lastHead (insert 1 S) = max (lastHead S) 1 := by
    apply le_antisymm
    · have hm := Finset.max'_mem (insert 0 (insert 1 S)) (Finset.insert_nonempty _ _)
      change lastHead (insert 1 S) ∈ insert 0 (insert 1 S) at hm
      rcases Finset.mem_insert.mp hm with hz | hs
      · rw [hz]
        exact Fin.zero_le _
      · rcases Finset.mem_insert.mp hs with h1 | hs
        · rw [h1]
          exact le_max_right _ _
        · exact le_trans (Finset.le_max' _ _ (Finset.mem_insert_of_mem hs)) (le_max_left _ _)
    · apply max_le
      · apply Finset.max'_subset (Finset.insert_nonempty _ _)
        intro i hi
        rcases Finset.mem_insert.mp hi with hz | hs
        · exact Finset.mem_insert.mpr (Or.inl hz)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hs)
      · exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  rw [he]
  apply firstSwap_max_one
  intro heq
  have hm := Finset.max'_mem (insert 0 S) (Finset.insert_nonempty _ _)
  change lastHead S ∈ insert 0 S at hm
  rw [heq] at hm
  rcases Finset.mem_insert.mp hm with hz | hs
  · exact Fin.succ_ne_zero (0 : Fin (r + 1)) hz
  · exact hS hs

theorem treeMax_firstSwap_insert_one (w : Fin (r + 1 + 1) → ℝ)
    (S : Finset (Fin (r + 1 + 1))) (hS : (1 : Fin (r + 1 + 1)) ∉ S) :
    treeMax (fun i => w (firstSwap r i)) (insert 1 S) = treeMax w S := by
  unfold treeMax
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · subst j
    change max (w (firstSwap r (parent (insert 1 S) 1))) (w (firstSwap r 1)) =
      max (w (parent S 1)) (w 1)
    rw [parent_one, parent_one]
    simp only [firstSwap, Equiv.swap_apply_left, Equiv.swap_apply_right, max_comm]
  · have hlt : (1 : Fin (r + 1 + 1)) < j.succ := by
      have hv : j.val ≠ 0 := fun he => hj (Fin.ext he)
      change 1 < j.val + 1
      exact Nat.succ_lt_succ (Nat.pos_of_ne_zero hv)
    dsimp only
    rw [firstSwap_parent_insert_one S hS _ hlt]
    have hfix : firstSwap r j.succ = j.succ :=
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j) (ne_of_gt hlt)
    rw [hfix]

/-- Removing the root from the base gives the same support function on the
paired words. The equality is pointwise for arbitrary real vertex values. -/
theorem rootPointedMax_firstSwap_insert_one (w : Fin (r + 1 + 1) → ℝ)
    (S : Finset (Fin (r + 1 + 1))) (hS : (1 : Fin (r + 1 + 1)) ∉ S) :
    baseMax (fun i => w (firstSwap r i)) (insert 1 S) - w (firstSwap r 0) =
      baseMax w S - w 0 := by
  unfold baseMax pointedMax
  rw [treeMax_firstSwap_insert_one w S hS]
  dsimp only
  rw [firstSwap_lastHead_insert_one S hS,
    Fintype.sum_equiv (firstSwap r) (fun i => w (firstSwap r i)) w (fun _ => rfl)]
  ring

end MaxNN.Caterpillar
