import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Defs
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.GraphKey
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.HeadOrder
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.HeadEndpoints
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.FiniteCombinatorics
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Count
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Reversal
import MaxNN.Constructions.Paramid.Caterpillar.Block.Index
import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing
import Mathlib.Data.Finset.Sort

/-!
# From decorated words to canonical caterpillar spines

This file removes the ordering of pendant vertices from a decorated word.  Its
head positions are `insert 0 S`, in increasing order; the apex is `π 0`; and a
remaining vertex is attached to the image of its last preceding head.  Thus
the construction is a direct finite map, with no choice of representatives.
-/

namespace MaxNN.Caterpillar.Corrections

variable {r : ℕ}

/-- The block-head positions of a decorated word. -/
def wordHeadPositions (w : WordIndex r) : Finset (Fin (r + 1)) :=
  insert 0 w.2.1

/-- The number of internal spine steps after removing the two mandatory
endpoint heads. -/
def wordSpineLength (w : WordIndex r) : ℕ :=
  w.2.1.card - 1

private theorem wordCuts_spec (w : WordIndex r) :
    w.2.1 ⊆ cutPositions r ∧ w.2.1 ≠ ∅ :=
  mem_admissibleCuts_iff.mp w.2.2

theorem zero_not_mem_wordCuts (w : WordIndex r) : (0 : Fin (r + 1)) ∉ w.2.1 := by
  intro h0
  exact (mem_cutPositions_iff.mp ((wordCuts_spec w).1 h0)) rfl

theorem wordCuts_card_pos (w : WordIndex r) : 0 < w.2.1.card :=
  Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (wordCuts_spec w).2)

theorem wordHeadPositions_card (w : WordIndex r) :
    (wordHeadPositions w).card = wordSpineLength w + 2 := by
  rw [wordHeadPositions, Finset.card_insert_of_not_mem (zero_not_mem_wordCuts w)]
  unfold wordSpineLength
  have hpos := wordCuts_card_pos w
  have hsub : w.2.1.card - 1 + 1 = w.2.1.card :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
  calc
    w.2.1.card + 1 = (w.2.1.card - 1 + 1) + 1 := by rw [hsub]
    _ = w.2.1.card - 1 + 2 := by omega

theorem wordSpineLength_lt (w : WordIndex r) : wordSpineLength w < r := by
  have hcard : w.2.1.card ≤ (cutPositions r).card :=
    Finset.card_le_of_subset (wordCuts_spec w).1
  have hcut : (cutPositions r).card = r := by
    unfold cutPositions
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  rw [hcut] at hcard
  unfold wordSpineLength
  have hpos := wordCuts_card_pos w
  exact (Nat.sub_lt hpos (by decide)).trans_le hcard

/-- The labelled head vertices, with the position order forgotten. -/
def wordHeads (w : WordIndex r) : Finset (Fin (r + 1 + 1)) :=
  (wordHeadPositions w).image fun i => w.1 i.succ

theorem wordHeads_card (w : WordIndex r) :
    (wordHeads w).card = wordSpineLength w + 2 := by
  rw [wordHeads, Finset.card_image_of_injective]
  · exact wordHeadPositions_card w
  · exact w.1.injective.comp (Fin.succ_injective (r + 1))

/-- The head vertices in increasing block-position order. -/
noncomputable def wordHeadOrder (w : WordIndex r) :
    Fin (wordSpineLength w + 2) ≃ ↑(wordHeads w) :=
  ((wordHeadPositions w).orderIsoOfFin (wordHeadPositions_card w)).toEquiv.trans
    (finsetImageEquiv (wordHeadPositions w) (fun i => w.1 i.succ)
      (w.1.injective.comp (Fin.succ_injective (r + 1))))

@[simp] theorem wordHeadOrder_apply (w : WordIndex r)
    (i : Fin (wordSpineLength w + 2)) :
    ((wordHeadOrder w i : ↑(wordHeads w)) : Fin (r + 1 + 1)) =
      w.1 (((wordHeadPositions w).orderIsoOfFin (wordHeadPositions_card w) i).1.succ) := by
  rfl

theorem wordApex_not_mem_wordHeads (w : WordIndex r) : w.1 0 ∉ wordHeads w := by
  intro h
  obtain ⟨p, _hp, he⟩ := Finset.mem_image.mp h
  have := w.1.injective he
  exact Fin.succ_ne_zero p this

/-- The base-word position of a non-apex simplex vertex. -/
def wordBasePosition (w : WordIndex r) (v : Fin (r + 1 + 1))
    (hv : v ≠ w.1 0) : Fin (r + 1) :=
  (w.1.symm v).pred (by
    intro h
    apply hv
    rw [← w.1.apply_symm_apply v, h])

@[simp] theorem wordBasePosition_succ (w : WordIndex r) (i : Fin (r + 1)) :
    wordBasePosition w (w.1 i.succ) (by exact fun h => Fin.succ_ne_zero i (w.1.injective h)) = i := by
  simp [wordBasePosition]

theorem wordPerm_basePosition_succ (w : WordIndex r) (v : Fin (r + 1 + 1))
    (hv : v ≠ w.1 0) : w.1 (wordBasePosition w v hv).succ = v := by
  unfold wordBasePosition
  rw [Fin.succ_pred, w.1.apply_symm_apply]

private def wordLeafPosition (w : WordIndex r)
    (v : SpineLeaves (wordHeads w) ⟨w.1 0, wordApex_not_mem_wordHeads w⟩) :
    Fin (r + 1) :=
  wordBasePosition w v.1 v.2.2

private theorem wordLeafPosition_not_mem (w : WordIndex r)
    (v : SpineLeaves (wordHeads w) ⟨w.1 0, wordApex_not_mem_wordHeads w⟩) :
    wordLeafPosition w v ∉ wordHeadPositions w := by
  intro hp
  apply v.2.1
  refine Finset.mem_image.mpr ⟨wordLeafPosition w v, hp, ?_⟩
  exact wordPerm_basePosition_succ w v.1 v.2.2

private def wordLeafAttachment (w : WordIndex r)
    (v : SpineLeaves (wordHeads w) ⟨w.1 0, wordApex_not_mem_wordHeads w⟩) :
    ↑(wordHeads w) :=
  ⟨w.1 (parent w.2.1 (wordLeafPosition w v)).succ,
    Finset.mem_image.mpr
      ⟨parent w.2.1 (wordLeafPosition w v), parent_mem_insert _ _, rfl⟩⟩

/-- The canonical oriented spine carried by a decorated word.  The data has
forgotten all order among leaves attached to the same head. -/
noncomputable def wordSpineData (w : WordIndex r) :
    SpineData (r + 1 + 1) (wordSpineLength w) where
  heads := wordHeads w
  card_heads := wordHeads_card w
  order := wordHeadOrder w
  apex := ⟨w.1 0, wordApex_not_mem_wordHeads w⟩
  attach := wordLeafAttachment w

@[simp] theorem wordSpineData_heads (w : WordIndex r) :
    (wordSpineData w).heads = wordHeads w := rfl

@[simp] theorem wordSpineData_apex (w : WordIndex r) :
    (wordSpineData w).apex.1 = w.1 0 := rfl

@[simp] theorem wordSpineData_order (w : WordIndex r)
    (i : Fin (wordSpineLength w + 2)) :
    ((wordSpineData w).order i : Fin (r + 1 + 1)) =
      w.1 (((wordHeadPositions w).orderIsoOfFin (wordHeadPositions_card w) i).1.succ) := by
  rfl

@[simp] theorem wordSpineData_attach (w : WordIndex r)
    (v : SpineLeaves (wordHeads w) ⟨w.1 0, wordApex_not_mem_wordHeads w⟩) :
    ((wordSpineData w).attach v : Fin (r + 1 + 1)) =
      w.1 (parent w.2.1 (wordLeafPosition w v)).succ := by
  rfl

theorem wordSpineData_order_zero (w : WordIndex r) :
    ((wordSpineData w).order 0).1 = wordFirstHead w := by
  rw [wordSpineData_order]
  unfold wordHeadPositions wordFirstHead
  rw [headOrderIso_zero]

theorem wordSpineData_order_last (w : WordIndex r) :
    ((wordSpineData w).order (Fin.last (wordSpineLength w + 1))).1 =
      wordLastHead w := by
  rw [wordSpineData_order]
  unfold wordHeadPositions wordLastHead
  rw [headOrderIso_last]

private theorem wordEdge_of_head_mem_shapeEdges (w : WordIndex r) (j : Fin r)
    (hj : j.succ ∈ wordHeadPositions w) :
    wordGraphEdge w j ∈ (wordSpineData w).shapeEdges := by
  let C := wordHeadPositions w
  let e := C.orderIsoOfFin (wordHeadPositions_card w)
  let t : Fin (wordSpineLength w + 2) := e.symm ⟨j.succ, hj⟩
  have ht : e t = ⟨j.succ, hj⟩ := e.apply_symm_apply _
  have ht0 : t ≠ 0 := by
    intro hzero
    have hv := congrArg Subtype.val ht
    rw [hzero] at hv
    have hz : (C.orderEmbOfFin (wordHeadPositions_card w)
        (0 : Fin (wordSpineLength w + 2))) = 0 := by
      dsimp only [C, wordHeadPositions]
      exact headOrder_zero w.2.1 (wordHeadPositions_card w)
    change C.orderEmbOfFin (wordHeadPositions_card w) 0 = j.succ at hv
    rw [hz] at hv
    exact Fin.succ_ne_zero j hv.symm
  let i : Fin (wordSpineLength w + 1) := t.pred ht0
  have hisucc : i.succ = t := Fin.succ_pred t ht0
  have hchild : C.orderEmbOfFin (wordHeadPositions_card w) i.succ = j.succ := by
    rw [hisucc]
    exact congrArg Subtype.val ht
  have hparent : parent w.2.1 j.succ =
      C.orderEmbOfFin (wordHeadPositions_card w) i.castSucc := by
    rw [← hchild]
    dsimp only [C, wordHeadPositions]
    exact parent_headOrder_succ w.2.1 (wordHeadPositions_card w) i
  apply Finset.mem_union_left
  refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
  rw [wordSpineData_order, wordSpineData_order]
  change sortedPair
      (w.1 (C.orderEmbOfFin (wordHeadPositions_card w) i.castSucc).succ)
      (w.1 (C.orderEmbOfFin (wordHeadPositions_card w) i.succ).succ) =
    sortedPair (w.1 (parent w.2.1 j.succ).succ) (w.1 j.succ.succ)
  rw [hparent, hchild]

private theorem wordEdge_of_not_head_mem_shapeEdges (w : WordIndex r) (j : Fin r)
    (hj : j.succ ∉ wordHeadPositions w) :
    wordGraphEdge w j ∈ (wordSpineData w).shapeEdges := by
  have hnotheads : w.1 j.succ.succ ∉ wordHeads w := by
    intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    have hpos := Fin.succ_injective (r + 1) (w.1.injective he)
    exact hj (hpos ▸ hp)
  have hneapex : w.1 j.succ.succ ≠ w.1 0 := by
    intro h
    exact Fin.succ_ne_zero j.succ (w.1.injective h)
  let v : SpineLeaves (wordHeads w) ⟨w.1 0, wordApex_not_mem_wordHeads w⟩ :=
    ⟨w.1 j.succ.succ, hnotheads, hneapex⟩
  have hpos : wordLeafPosition w v = j.succ := by
    dsimp only [wordLeafPosition, v]
    exact wordBasePosition_succ w j.succ
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨v, Finset.mem_univ v, ?_⟩
  rw [wordSpineData_attach, hpos]
  change sortedPair (w.1 j.succ.succ) (w.1 (parent w.2.1 j.succ).succ) =
    sortedPair (w.1 (parent w.2.1 j.succ).succ) (w.1 j.succ.succ)
  unfold sortedPair
  simp only [min_comm, max_comm]

theorem wordGraphEdges_subset_shapeEdges (w : WordIndex r) :
    wordGraphEdges w ⊆ (wordSpineData w).shapeEdges := by
  intro edge hedge
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hedge
  by_cases hhead : j.succ ∈ wordHeadPositions w
  · exact wordEdge_of_head_mem_shapeEdges w j hhead
  · exact wordEdge_of_not_head_mem_shapeEdges w j hhead

theorem SpineData.shapeEdges_card_le {N s : ℕ} (d : SpineData N s) :
    d.shapeEdges.card ≤ (s + 1) + (N - (s + 2) - 1) := by
  classical
  have hspine : d.spineEdges.card ≤ s + 1 := by
    unfold SpineData.spineEdges
    exact Finset.card_image_le.trans_eq (by simp)
  have hleaf : d.leafEdges.card ≤ N - (s + 2) - 1 := by
    unfold SpineData.leafEdges
    apply Finset.card_image_le.trans_eq
    rw [Finset.card_univ, SpineData.card_leaves, d.card_heads]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hspine hleaf)

theorem wordGraphEdges_eq_shapeEdges (w : WordIndex r) :
    wordGraphEdges w = (wordSpineData w).shapeEdges := by
  apply Finset.eq_of_subset_of_card_le (wordGraphEdges_subset_shapeEdges w)
  rw [wordGraphEdges_card]
  have hs := wordSpineLength_lt w
  have h := SpineData.shapeEdges_card_le (wordSpineData w)
  have he : (wordSpineLength w + 1) +
      (r + 1 + 1 - (wordSpineLength w + 2) - 1) = r := by omega
  exact h.trans_eq he

theorem normalizedKey_wordKey_eq_shapeKey (w : WordIndex r) :
    normalizedKey (wordKey w) = SpineData.shapeKey (wordSpineData w) := by
  rw [normalizedKey_wordKey_eq_graphKey, SpineData.shapeKey,
    wordGraphEdges_eq_shapeEdges, wordSpineData_order_zero, wordSpineData_order_last]

end MaxNN.Caterpillar.Corrections
