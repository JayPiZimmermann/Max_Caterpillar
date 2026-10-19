import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Reversal

/-!
# The undirected graph key of a caterpillar word

After every simplex-difference label is oriented by its endpoint order, the
key of a caterpillar word remembers only its undirected tree, its apex, and
the two endpoints of its spine.  In particular it forgets the order of the
pendant leaves and the orientation of the spine.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidChain

variable {n r : ℕ}

noncomputable local instance reverseLabelDecidable (n : ℕ) :
    DecidablePred (reverseLabel (n := n)) := Classical.decPred _

/-- An undirected edge on `N` vertices, represented by its endpoints in
increasing order.

We keep the representation as a
plain pair because `sortedPair` supplies the canonical ordering everywhere
the type is used.
-/
abbrev GraphEdge (N : ℕ) := Fin N × Fin N

/-- Canonically order the endpoints of an undirected edge. -/
def sortedPair {N : ℕ} (a b : Fin N) : GraphEdge N := (min a b, max a b)

/-- The canonically oriented simplex difference carried by a graph edge. -/
noncomputable def graphEdgeVec (e : GraphEdge (n + 1)) : Fin n → ℝ :=
  toR (vtx e.1) - toR (vtx e.2)

/-- The key determined by an undirected tree, an apex, and the unordered
spine endpoints.  Symmetry in `p,q` is definitional up to commutativity of
addition.
-/
noncomputable def graphKey (E : Finset (GraphEdge (n + 1)))
    (p q : Fin (n + 1)) : RealKey n :=
  ((∑ e in E, toR (vtx e.2)) + toR (vtx p) + toR (vtx q) -
      ∑ a : Fin (n + 1), toR (vtx a),
    E.image graphEdgeVec)

theorem graphKey_swap (E : Finset (GraphEdge (n + 1))) (p q : Fin (n + 1)) :
    graphKey E q p = graphKey E p q := by
  ext i <;> simp [graphKey, add_comm, add_left_comm, add_assoc]

theorem graphEdgeVec_sortedPair (a b : Fin (n + 1)) :
    graphEdgeVec (sortedPair a b) =
      toR (vtx (min a b)) - toR (vtx (max a b)) := rfl

/-- The affine shift contributed when normalization reverses a label. -/
noncomputable def reverseShift (v : Fin n → ℝ) : Fin n → ℝ := by
  classical
  exact if reverseLabel v then v else 0

/-- Orienting a nontrivial simplex difference is the same as sorting its
two endpoints. -/
theorem orientedLabel_simplex_sub_eq_graphEdgeVec {a b : Fin (n + 1)}
    (hab : a ≠ b) :
    orientedLabel (toR (vtx a) - toR (vtx b)) =
      graphEdgeVec (sortedPair a b) := by
  classical
  unfold orientedLabel graphEdgeVec sortedPair
  rw [reverseLabel_simplex_sub_iff hab]
  rcases lt_or_gt_of_ne hab with hab' | hba
  · simp [hab', hab'.le, not_lt_of_ge hab'.le]
  · simp [hba, hba.le, not_lt_of_ge hba.le]

/-- The larger endpoint equals the child endpoint plus the normalization
shift of the directed edge from `a` to `b`. -/
theorem sortedPair_max_eq_child_add_reverseShift {a b : Fin (n + 1)}
    (hab : a ≠ b) :
    toR (vtx (sortedPair a b).2) =
      toR (vtx b) + reverseShift (toR (vtx a) - toR (vtx b)) := by
  classical
  unfold sortedPair reverseShift
  rcases lt_or_gt_of_ne hab with hab' | hba
  · have hnrev : ¬ reverseLabel (toR (vtx a) - toR (vtx b)) :=
      (reverseLabel_simplex_sub_iff hab).not.mpr (not_lt_of_ge hab'.le)
    simp [hab', hab'.le, not_lt_of_ge hab'.le, hnrev]
  · have hrev : reverseLabel (toR (vtx a) - toR (vtx b)) :=
      (reverseLabel_simplex_sub_iff hab).mpr hba
    simp [hba, hba.le, not_lt_of_ge hba.le, hrev]

/-- The underlying undirected edge in a decorated caterpillar word. -/
def wordGraphEdge (w : WordIndex r) (j : Fin r) : GraphEdge (r + 1 + 1) :=
  sortedPair
    (w.1 (parent w.2.1 j.succ).succ)
    (w.1 j.succ.succ)

/-- The undirected labelled tree carried by a decorated word. -/
noncomputable def wordGraphEdges (w : WordIndex r) : Finset (GraphEdge (r + 1 + 1)) :=
  Finset.univ.image (wordGraphEdge w)

/-- The first endpoint of the oriented spine. -/
def wordFirstHead (w : WordIndex r) : Fin (r + 1 + 1) :=
  w.1 (0 : Fin (r + 1)).succ

/-- The last endpoint of the oriented spine. -/
def wordLastHead (w : WordIndex r) : Fin (r + 1 + 1) :=
  w.1 (lastHead w.2.1).succ

theorem wordGraphEdge_endpoints_ne (w : WordIndex r) (j : Fin r) :
    w.1 (parent w.2.1 j.succ).succ ≠ w.1 j.succ.succ := by
  intro h
  have h' := w.1.injective h
  have h'' := Fin.succ_injective (r + 1) h'
  exact (ne_of_lt (parent_lt (Fin.succ_pos j))) h''

theorem orientedLabel_word_edgeVec (w : WordIndex r) (j : Fin r) :
    orientedLabel (edgeVecs (wordBase w) w.2.1 j) =
      graphEdgeVec (wordGraphEdge w j) := by
  unfold edgeVecs wordBase wordGraphEdge
  exact orientedLabel_simplex_sub_eq_graphEdgeVec
    (wordGraphEdge_endpoints_ne w j)

theorem wordGraphEdge_injective (w : WordIndex r) :
    Function.Injective (wordGraphEdge w) := by
  intro j k h
  have hv : graphEdgeVec (wordGraphEdge w j) =
      graphEdgeVec (wordGraphEdge w k) := congrArg graphEdgeVec h
  rw [← orientedLabel_word_edgeVec, ← orientedLabel_word_edgeVec] at hv
  have hinj : Set.InjOn orientedLabel
      (wordLabels w : Set (Fin (r + 1) → ℝ)) :=
    orientedLabel_injOn (fun _ hu _ hv' => wordLabels_ne_neg w hu hv')
  have hj : edgeVecs (wordBase w) w.2.1 j ∈ wordLabels w :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hk : edgeVecs (wordBase w) w.2.1 k ∈ wordLabels w :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have he := hinj hj hk hv
  exact edgeVecs_simplex_injective (fun i => w.1 i.succ)
    (w.1.injective.comp (Fin.succ_injective (r + 1))) w.2.1 he

theorem wordGraphEdges_card (w : WordIndex r) : (wordGraphEdges w).card = r := by
  unfold wordGraphEdges
  rw [Finset.card_image_of_injective _ (wordGraphEdge_injective w),
    Finset.card_univ, Fintype.card_fin]

theorem graphKey_wordGraphEdges_labels (w : WordIndex r) :
    (graphKey (wordGraphEdges w) (wordFirstHead w) (wordLastHead w)).2 =
      (wordLabels w).image orientedLabel := by
  classical
  unfold graphKey wordGraphEdges wordLabels
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro j _hj
  exact (orientedLabel_word_edgeVec w j).symm

private theorem sum_wordGraphEdges_max (w : WordIndex r) :
    ∑ e in wordGraphEdges w, toR (vtx e.2) =
      ∑ j : Fin r, (toR (vtx (w.1 j.succ.succ)) +
        reverseShift (edgeVecs (wordBase w) w.2.1 j)) := by
  classical
  unfold wordGraphEdges
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _hj
    unfold wordGraphEdge edgeVecs wordBase
    exact sortedPair_max_eq_child_add_reverseShift
      (wordGraphEdge_endpoints_ne w j)
  · intro j _hj k _hk
    exact fun h => wordGraphEdge_injective w h

private theorem sum_wordLabels_reverse (w : WordIndex r) :
    ∑ v in (wordLabels w).filter reverseLabel, v =
      ∑ j : Fin r, reverseShift (edgeVecs (wordBase w) w.2.1 j) := by
  classical
  unfold wordLabels reverseShift
  rw [Finset.sum_filter, Finset.sum_image]
  intro j _hj k _hk h
  exact edgeVecs_simplex_injective (fun i => w.1 i.succ)
    (w.1.injective.comp (Fin.succ_injective (r + 1))) w.2.1 h

private theorem sum_word_children (w : WordIndex r) :
    ∑ j : Fin r, toR (vtx (w.1 j.succ.succ)) =
      (∑ a : Fin (r + 1 + 1), toR (vtx a)) -
        toR (vtx (w.1 0)) - toR (vtx (w.1 (0 : Fin (r + 1)).succ)) := by
  classical
  have hperm : (∑ a : Fin (r + 1 + 1), toR (vtx (w.1 a))) =
      ∑ a : Fin (r + 1 + 1), toR (vtx a) := by
    exact Equiv.sum_comp w.1 (fun a => toR (vtx a))
  have htail := Fin.sum_univ_succ
    (f := fun i : Fin (r + 1) => toR (vtx (w.1 i.succ)))
  have hall := Fin.sum_univ_succ
    (f := fun a : Fin (r + 1 + 1) => toR (vtx (w.1 a)))
  rw [hperm] at hall
  simp only [Fin.cases_zero, Fin.cases_succ] at htail hall
  rw [htail] at hall
  rw [hall]
  abel

private theorem graphKey_wordGraphEdges_gamma (w : WordIndex r) :
    (graphKey (wordGraphEdges w) (wordFirstHead w) (wordLastHead w)).1 =
      wordGamma w + ∑ v in (wordLabels w).filter reverseLabel, v := by
  classical
  rw [sum_wordLabels_reverse]
  change (∑ e in wordGraphEdges w, toR (vtx e.2)) +
      toR (vtx (wordFirstHead w)) + toR (vtx (wordLastHead w)) -
        ∑ a : Fin (r + 1 + 1), toR (vtx a) =
    wordGamma w + ∑ j : Fin r,
      reverseShift (edgeVecs (wordBase w) w.2.1 j)
  rw [sum_wordGraphEdges_max, Finset.sum_add_distrib, sum_word_children]
  unfold wordGamma wordLastHead wordFirstHead wordBase wordApex
  abel

/-- The normalized paramid key of a decorated word factors through its
undirected tree, apex and unordered spine endpoints. -/
theorem normalizedKey_wordKey_eq_graphKey (w : WordIndex r) :
    normalizedKey (wordKey w) =
      graphKey (wordGraphEdges w) (wordFirstHead w) (wordLastHead w) := by
  classical
  unfold normalizedKey wordKey
  apply Prod.ext
  · exact (graphKey_wordGraphEdges_gamma w).symm
  · exact (graphKey_wordGraphEdges_labels w).symm

end MaxNN.Caterpillar.Corrections
