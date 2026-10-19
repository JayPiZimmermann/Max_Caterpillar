import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing

/-! # Base values with a single crossing edge

This is the scalar calculation used by the facet-pattern DFS branch. It holds
for every word length; no simplex embedding or normal-direction hypothesis is
needed. The distinguished edge need not actually cross.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ}

theorem baseMax_eq_of_unique_edge (S : Finset (Fin (r + 1)))
    (w : Fin (r + 1) → ℝ) (j : Fin r)
    (hother : ∀ k : Fin r, k ≠ j → w k.succ = w (parent S k.succ)) :
    baseMax w S = max (w (parent S j.succ)) (w j.succ) - w j.succ + w (lastHead S) := by
  rw [baseMax_eq_sum_parent_diff]
  congr 1
  apply Finset.sum_eq_single j
  · intro k _ hk
    rw [hother k hk, max_self, sub_self]
  · intro h
    exact False.elim (h (Finset.mem_univ j))

theorem baseMax_unique_cut (S : Finset (Fin (r + 1)))
    (w : Fin (r + 1) → ℝ) (j : Fin r) (hj : j.succ ∈ S)
    (hother : ∀ k : Fin r, k ≠ j → w k.succ = w (parent S k.succ)) :
    baseMax w S = max (w 0) (w j.succ) := by
  have hw := unique_edge_cut_values S w j hj hother
  have hparent : w (parent S j.succ) = w 0 := by
    rw [hw, if_pos (parent_lt (Fin.succ_pos j))]
  have hlast : w (lastHead S) = w j.succ := by
    have hle : j.succ ≤ lastHead S := Finset.le_max' _ _ (Finset.mem_insert_of_mem hj)
    rw [hw, if_neg (not_lt.mpr hle)]
  rw [baseMax_eq_of_unique_edge S w j hother, hparent, hlast, sub_add_cancel]

end MaxNN.Caterpillar
