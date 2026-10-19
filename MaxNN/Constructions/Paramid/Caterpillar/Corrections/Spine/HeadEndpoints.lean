import MaxNN.Constructions.Paramid.Caterpillar.Words
import Mathlib.Data.Finset.Sort

/-! # Endpoints of the increasing list of block heads -/

namespace MaxNN.Caterpillar.Corrections

variable {r k : ℕ}

theorem headOrderIso_zero (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) :
    (((insert 0 S).orderIsoOfFin hcard 0).1 : Fin (r + 1)) = 0 := by
  let e := (insert 0 S).orderIsoOfFin hcard
  let z : ↑(insert 0 S) := ⟨0, Finset.mem_insert_self _ _⟩
  have hz := e.monotone (Fin.zero_le (e.symm z))
  rw [e.apply_symm_apply] at hz
  exact le_antisymm hz (Fin.zero_le _)

theorem headOrderEmb_zero (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) :
    (insert 0 S).orderEmbOfFin hcard 0 = 0 :=
  headOrderIso_zero S hcard

theorem headOrderEmb_last (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) :
    (insert 0 S).orderEmbOfFin hcard (Fin.last (k + 1)) = lastHead S := by
  have h := Finset.orderEmbOfFin_last hcard (by omega : 0 < k + 2)
  have hi : (⟨k + 2 - 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := by
    apply Fin.ext
    simp
  rw [hi] at h
  exact h

theorem headOrderIso_last (S : Finset (Fin (r + 1)))
    (hcard : (insert 0 S).card = k + 2) :
    (((insert 0 S).orderIsoOfFin hcard (Fin.last (k + 1))).1 : Fin (r + 1)) =
      lastHead S :=
  headOrderEmb_last S hcard

end MaxNN.Caterpillar.Corrections
