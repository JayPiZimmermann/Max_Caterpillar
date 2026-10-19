import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Defs
import Mathlib.Data.Finset.Sort

/-!
# Increasing enumeration of caterpillar spine heads

The set `insert 0 S` consists exactly of the heads of the ordered caterpillar.
Its increasing enumeration starts at the root, ends at `lastHead S`, and every
two consecutive enumerated heads form one directed spine edge according to
`parent S`.
-/

namespace MaxNN.Caterpillar.Corrections

variable {r k : ℕ}

/-- The increasing enumeration of all heads begins at the root. -/
theorem headOrder_zero (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) :
    (insert 0 S).orderEmbOfFin hcard (0 : Fin (k + 2)) = 0 := by
  let hz : 0 < k + 2 := by omega
  calc
    (insert 0 S).orderEmbOfFin hcard (0 : Fin (k + 2)) =
        (insert 0 S).orderEmbOfFin hcard ⟨0, hz⟩ := by congr 1
    _ = (insert 0 S).min' (Finset.card_pos.mp (hcard.symm ▸ hz)) :=
      Finset.orderEmbOfFin_zero hcard hz
    _ = 0 := by
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_insert_self 0 S)
      · exact Fin.zero_le _

/-- The increasing enumeration of all heads ends at `lastHead S`. -/
theorem headOrder_last (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) :
    (insert 0 S).orderEmbOfFin hcard (Fin.last (k + 1)) = lastHead S := by
  let hz : 0 < k + 2 := by omega
  calc
    (insert 0 S).orderEmbOfFin hcard (Fin.last (k + 1)) =
        (insert 0 S).orderEmbOfFin hcard
          ⟨k + 2 - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ := by congr 1
    _ = (insert 0 S).max' (Finset.card_pos.mp (hcard.symm ▸ hz)) :=
      Finset.orderEmbOfFin_last hcard hz
    _ = lastHead S := rfl

/-- There is no selected head strictly between consecutive values of the
increasing head enumeration. -/
theorem headOrder_le_of_lt_succ (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) (i : Fin (k + 1))
    {q : Fin (r + 1)} (hq : q ∈ insert 0 S)
    (hlt : q < (insert 0 S).orderEmbOfFin hcard i.succ) :
    q ≤ (insert 0 S).orderEmbOfFin hcard i.castSucc := by
  have hrange : q ∈ Set.range ((insert 0 S).orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin]
    exact hq
  rcases hrange with ⟨t, rfl⟩
  have ht : t < i.succ :=
    ((insert 0 S).orderEmbOfFin hcard).lt_iff_lt.mp hlt
  apply ((insert 0 S).orderEmbOfFin hcard).monotone
  apply Fin.le_iff_val_le_val.mpr
  exact Nat.le_of_lt_succ (by simpa using ht)

/-- Consecutive values of the increasing head enumeration are precisely a
child head and its `parent`. -/
theorem parent_headOrder_succ (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) (i : Fin (k + 1)) :
    parent S ((insert 0 S).orderEmbOfFin hcard i.succ) =
      (insert 0 S).orderEmbOfFin hcard i.castSucc := by
  let C : Finset (Fin (r + 1)) := insert 0 S
  let e : Fin (k + 2) ↪o Fin (r + 1) := C.orderEmbOfFin hcard
  have hprev_mem : e i.castSucc ∈ C :=
    Finset.orderEmbOfFin_mem C hcard i.castSucc
  have hstep : e i.castSucc < e i.succ :=
    e.strictMono (Fin.castSucc_lt_succ i)
  have hprev_filtered : e i.castSucc ∈ insert 0 (S.filter fun q => q < e i.succ) := by
    rcases Finset.mem_insert.mp hprev_mem with hzero | hS
    · exact Finset.mem_insert.mpr (Or.inl hzero)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hS, hstep⟩))
  unfold parent
  apply le_antisymm
  · apply Finset.max'_le
    intro q hq
    rcases Finset.mem_insert.mp hq with hzero | hS
    · rw [hzero]
      exact Fin.zero_le _
    · have hq' := Finset.mem_filter.mp hS
      exact headOrder_le_of_lt_succ S hcard i
        (Finset.mem_insert_of_mem hq'.1) hq'.2
  · exact Finset.le_max' _ _ hprev_filtered

end MaxNN.Caterpillar.Corrections
