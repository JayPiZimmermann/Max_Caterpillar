import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Defs
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.GraphKey
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.FiniteCombinatorics

/-!
# Reversing canonical caterpillar spines

The edges of a `SpineData` are recorded as unordered endpoint pairs.  Reversing
the spine order therefore preserves its graph and exchanges its two endpoints.
The reversal is a fixed-point-free involution, so every reversal-invariant
image has at most half as many elements as the oriented data type.
-/

namespace MaxNN.Caterpillar.Corrections

namespace SpineData

variable {N s : ℕ}

/-- Sort the endpoints of an undirected edge.  This version is polymorphic in
the number of vertices, avoiding subtraction in the `SpineData` API. -/
def sortedEdge (a b : Fin N) : Fin N × Fin N := (min a b, max a b)

@[simp] theorem sortedEdge_comm (a b : Fin N) : sortedEdge a b = sortedEdge b a := by
  simp only [sortedEdge, min_comm, max_comm]

/-- The consecutive edges in the ordered spine. -/
noncomputable def spineEdges (d : SpineData N s) : Finset (Fin N × Fin N) :=
  Finset.univ.image fun i : Fin (s + 1) =>
    sortedEdge (d.order i.castSucc).1 (d.order i.succ).1

/-- The edge joining every non-head, non-apex vertex to its chosen head. -/
noncomputable def leafEdges (d : SpineData N s) : Finset (Fin N × Fin N) :=
  Finset.univ.image fun v : SpineLeaves d.heads d.apex =>
    sortedEdge v.1 (d.attach v).1

/-- The undirected caterpillar tree carried by canonical spine data. -/
noncomputable def shapeEdges (d : SpineData N s) : Finset (Fin N × Fin N) :=
  spineEdges d ∪ leafEdges d

/-- Reversal of a finite linear order. -/
def finRevEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- Reverse only the order of the spine.  Heads, apex and leaf attachments are
literally unchanged. -/
def reverseSpineData (d : SpineData N s) : SpineData N s :=
  { d with order := (finRevEquiv (s + 2)).trans d.order }

@[simp] theorem reverseSpineData_heads (d : SpineData N s) :
    (reverseSpineData d).heads = d.heads := rfl

@[simp] theorem reverseSpineData_apex (d : SpineData N s) :
    (reverseSpineData d).apex = d.apex := rfl

@[simp] theorem reverseSpineData_attach (d : SpineData N s) :
    (reverseSpineData d).attach = d.attach := rfl

@[simp] theorem reverseSpineData_order (d : SpineData N s) (i : Fin (s + 2)) :
    (reverseSpineData d).order i = d.order (Fin.rev i) := rfl

@[simp] theorem reverseSpineData_involutive :
    Function.Involutive (reverseSpineData : SpineData N s → SpineData N s) := by
  intro d
  apply SpineData.ext
  · rfl
  · exact heq_of_eq (by
      apply Equiv.ext
      intro i
      change d.order (Fin.rev (Fin.rev i)) = d.order i
      rw [Fin.rev_rev])
  · rfl
  · rfl

theorem reverseSpineData_ne (d : SpineData N s) : reverseSpineData d ≠ d := by
  intro h
  have hv := congrArg (fun q : SpineData N s => (q.order 0).1) h
  change (d.order (Fin.rev 0)).1 = (d.order 0).1 at hv
  have hs : d.order (Fin.rev 0) = d.order 0 := Subtype.ext hv
  have hi := d.order.injective hs
  have hiv := congrArg Fin.val hi
  simp only [Fin.val_rev, Fin.val_zero] at hiv
  omega

private theorem rev_castSucc (i : Fin (s + 1)) :
    Fin.rev i.castSucc = (Fin.rev i).succ := by
  apply Fin.ext
  simp only [Fin.val_rev, Fin.coe_castSucc, Fin.val_succ]
  have hi := i.isLt
  have hle : i.val + 1 ≤ s + 1 := by omega
  simpa only [Nat.succ_eq_add_one] using Nat.succ_sub hle

private theorem rev_succ (i : Fin (s + 1)) :
    Fin.rev i.succ = (Fin.rev i).castSucc := by
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
  exact Nat.succ_sub_succ_eq_sub (s + 1) (i.val + 1)

theorem spineEdges_reverseSpineData (d : SpineData N s) :
    spineEdges (reverseSpineData d) = spineEdges d := by
  classical
  ext e
  simp only [spineEdges, Finset.mem_image, Finset.mem_univ, true_and,
    reverseSpineData_order]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.rev i, ?_⟩
    rw [rev_castSucc, rev_succ]
    exact sortedEdge_comm _ _
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.rev i, ?_⟩
    rw [rev_castSucc, rev_succ]
    simp only [Fin.rev_rev]
    exact sortedEdge_comm _ _

@[simp] theorem leafEdges_reverseSpineData (d : SpineData N s) :
    leafEdges (reverseSpineData d) = leafEdges d := rfl

@[simp] theorem shapeEdges_reverseSpineData (d : SpineData N s) :
    shapeEdges (reverseSpineData d) = shapeEdges d := by
  simp only [shapeEdges, spineEdges_reverseSpineData, leafEdges_reverseSpineData]

/-- The key of a canonical caterpillar shape. -/
noncomputable def shapeKey {n : ℕ} (d : SpineData (n + 1) s) : RealKey n :=
  graphKey (shapeEdges d) (d.order 0).1 (d.order (Fin.last (s + 1))).1

@[simp] theorem shapeKey_reverseSpineData {n : ℕ} (d : SpineData (n + 1) s) :
    shapeKey (reverseSpineData d) = shapeKey d := by
  unfold shapeKey
  rw [shapeEdges_reverseSpineData]
  have hzero : Fin.rev (0 : Fin (s + 2)) = Fin.last (s + 1) := by
    apply Fin.ext
    simp
  have hlast : Fin.rev (Fin.last (s + 1)) = (0 : Fin (s + 2)) := by
    apply Fin.ext
    simp
  rw [reverseSpineData_order, reverseSpineData_order, hzero, hlast]
  exact graphKey_swap _ _ _

/-- Generic two-element fiber bound for the image of a fixed-point-free map
that preserves the indexed value.  Spine reversal supplies such a map. -/
theorem card_image_le_half_of_fixedPointFree {I A : Type*} [Fintype I]
    [DecidableEq A] (e : I → I) (f : I → A)
    (hne : ∀ i, e i ≠ i) (hf : ∀ i, f (e i) = f i) :
    (Finset.univ.image f).card ≤ Fintype.card I / 2 := by
  classical
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  rw [Nat.mul_comm]
  apply card_image_mul_le_of_fiber_card 2 f
  intro a ha
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
  have hsubset : {i, e i} ⊆ Finset.univ.filter fun j => f j = f i := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp
    · rw [Finset.mem_singleton.mp hj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hf i
  have hpair : ({i, e i} : Finset I).card = 2 := by
    have hnot : i ∉ ({e i} : Finset I) := by
      simpa only [Finset.mem_singleton] using (hne i).symm
    rw [Finset.card_insert_of_not_mem hnot, Finset.card_singleton]
  rw [← hpair]
  exact Finset.card_le_of_subset hsubset

/-- The set of distinct graph keys carried by spine data of a fixed length. -/
noncomputable def shapeKeys (n s : ℕ) : Finset (RealKey n) :=
  Finset.univ.image fun d : SpineData (n + 1) s => shapeKey d

theorem card_shapeKeys_le_half (n s : ℕ) :
    (shapeKeys n s).card ≤ Fintype.card (SpineData (n + 1) s) / 2 := by
  exact card_image_le_half_of_fixedPointFree
    (reverseSpineData : SpineData (n + 1) s → SpineData (n + 1) s)
    (fun d : SpineData (n + 1) s => shapeKey d)
    reverseSpineData_ne shapeKey_reverseSpineData

end SpineData

end MaxNN.Caterpillar.Corrections
