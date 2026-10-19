import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# Counting canonical labelled caterpillars

The count separates the choices visible in `SpineData`: a head set, its linear
order, an apex outside it, and one head-valued attachment for every remaining
vertex.  In particular, no ordering of leaves inside an attachment fibre is
counted.
-/

namespace MaxNN.Caterpillar.Corrections

open scoped BigOperators

namespace SpineData

variable {N s : ℕ}

/-- Regard a leaf as a non-apex element of the complement of the head set. -/
def leavesEquivApexNe (H : Finset (Fin N)) (a : SpineApex H) :
    SpineLeaves H a ≃ {v : SpineApex H // v ≠ a} where
  toFun v :=
    ⟨⟨v.1, v.2.1⟩, by
      intro h
      exact v.2.2 (congrArg Subtype.val h)⟩
  invFun v :=
    ⟨v.1.1, v.1.2, by
      intro h
      apply v.2
      exact Subtype.ext h⟩
  left_inv v := by rfl
  right_inv v := by rfl

theorem card_apex (H : Finset (Fin N)) :
    Fintype.card (SpineApex H) = N - H.card := by
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    (Fintype.card_subtype_compl (fun x : Fin N => x ∈ H))

theorem card_leaves (H : Finset (Fin N)) (a : SpineApex H) :
    Fintype.card (SpineLeaves H a) = N - H.card - 1 := by
  calc
    Fintype.card (SpineLeaves H a) =
        Fintype.card {v : SpineApex H // v ≠ a} :=
      Fintype.card_congr (leavesEquivApexNe H a)
    _ = Fintype.card (SpineApex H) - 1 := by
      simpa only using (Set.card_ne_eq a)
    _ = N - H.card - 1 := by rw [card_apex]

theorem card_apex_attachment (H : Finset (Fin N)) :
    Fintype.card (Σ a : SpineApex H, SpineLeaves H a → ↑H) =
      (N - H.card) * H.card ^ (N - H.card - 1) := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_fun, Fintype.card_coe, card_leaves]
  rw [Finset.sum_const, Finset.card_univ, card_apex]
  rfl

theorem card_orders (H : SpineHeadSet N (s + 2)) :
    Fintype.card (Fin (s + 2) ≃ ↑H.1) = (s + 2).factorial := by
  simpa only [Fintype.card_fin] using
    Fintype.card_equiv (Finset.equivFinOfCardEq H.2).symm

/-- Exact number of oriented canonical caterpillar data with `s + 2` spine
heads.  This is the unhalved count; reversal of the spine is a separate,
fixed-point-free semantic symmetry. -/
theorem card_spineData (N s : ℕ) :
    Fintype.card (SpineData N s) =
      N.choose (s + 2) * (s + 2).factorial * (N - (s + 2)) *
        (s + 2) ^ (N - (s + 3)) := by
  classical
  rw [Fintype.card_congr (spineDataEquivSigma N s), Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_orders, card_apex_attachment]
  have hsub : N - (s + 2) - 1 = N - (s + 3) := by omega
  have hcard (H : SpineHeadSet N (s + 2)) : H.1.card = s + 2 := H.2
  simp_rw [hcard, hsub]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len]
  simp only [Fintype.card_fin]
  ring

end SpineData

end MaxNN.Caterpillar.Corrections
