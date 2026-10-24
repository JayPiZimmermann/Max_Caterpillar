import MaxCaterpillar.RationalWidth

/-! # Sparse caterpillar expansions in small arity

An exact search over the caterpillar vocabulary (`scripts/vocabulary_search.py`)
finds expansions of the maximum by very few normalized face functions.  The
identities below are proved for all real inputs by exhaustive case analysis
on the activation pattern; the compilation theorem then gives networks with
the existing first hidden layer:

* `N = 3`: `max₃ = x₁ + σ(x₂ - x₁ + σ(x₀ - x₂))`, widths `(7, 3)`;
* `N = 4`: three face functions, widths `(11, 5)`.

The general widths `(firstWidth N, secondWidth N)` are proved in
`Theorems.lean`; these are smaller widths for these arities.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom ParamidChain

/-! ## Labels in reduced coordinates -/

/-- The coordinate difference `e_a - e_b` in reduced coordinates. -/
noncomputable def lbl {n : ℕ} (a b : Fin (n + 1)) : Fin n → ℝ := toR (vtx a) - toR (vtx b)

theorem dot_lbl {n : ℕ} (a b : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    dot (lbl a b) ((CoordAux.coordT n).mulVec x) = x a - x b := by
  unfold lbl
  rw [SupportCut.dot_sub_left, dot_toR_vtx_coordT, dot_toR_vtx_coordT]
  ring

theorem lbl_simplexDifference {n : ℕ} (a b : Fin (n + 1)) : IsSimplexDifference (lbl a b) :=
  ⟨a, b, rfl⟩

theorem ratVec_lbl {n : ℕ} (a b : Fin (n + 1)) : RatVec (lbl a b) :=
  (ratVec_toR _).sub (ratVec_toR _)

theorem lbl_ne {n : ℕ} {a b c e : Fin (n + 1)} (x : Fin (n + 1) → ℝ)
    (h : x a - x b ≠ x c - x e) : lbl a b ≠ lbl c e := by
  intro he
  apply h
  rw [← dot_lbl a b x, ← dot_lbl c e x, he]

/-- A test point separating the labels used below. -/
noncomputable def ramp : Fin 4 → ℝ :=
  fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else 7

/-! ## Arity three -/

theorem max_three_eq (x : Fin 3 → ℝ) : MAX 3 x = max (max (x 0) (x 1)) (x 2) := by
  apply le_antisymm
  · refine MAX_le fun i => ?_
    fin_cases i
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_right _ _
  · exact max_le (max_le (le_MAX 3 x 0) (le_MAX 3 x 1)) (le_MAX 3 x 2)

theorem max_three_identity (x : Fin 3 → ℝ) :
    MAX 3 x = x 1 + relu (x 2 - x 1 + relu (x 0 - x 2)) := by
  rw [max_three_eq]
  unfold relu
  simp only [max_def]
  split_ifs <;> linarith

noncomputable def key3 : RealKey 2 := (lbl 2 1, {lbl 0 2})

theorem realUnitY_key3 (x : Fin 3 → ℝ) :
    realUnitY key3 x = relu (x 2 - x 1 + relu (x 0 - x 2)) := by
  rw [realUnitY_eq_relu]
  unfold realUnitArg key3
  rw [Finset.sum_singleton, dot_lbl, dot_lbl]
  rfl

/-- **Arity three.** Widths `(7, 3)`, rational weights,
zero biases. -/
theorem max_three_network :
    ∃ net : Network 3 (firstWidth 3) 3,
      (∀ x, net.eval x = Maximum 3 x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  apply compile_expansion_width (n := 2) {key3} (fun _ => 1) (coordCoef 1)
  · intro k hk v hv
    rw [Finset.mem_singleton.mp hk] at hv
    rw [Finset.mem_singleton.mp hv]
    exact lbl_simplexDifference _ _
  · intro k hk
    rw [Finset.mem_singleton.mp hk]
    exact (ratVec_toR _).sub (ratVec_toR _)
  · exact fun _ _ => Subfield.one_mem _
  · exact ratVec_coordCoef 1
  · intro x
    have h : auxiliary (coordCoef 1) x = x 1 := by
      unfold auxiliary; rw [sum_coordCoef, coordLin_feat]
    rw [Finset.sum_singleton, h, realUnitY_key3, one_mul]
    refine (max_three_identity x).trans ?_
    ring
  · exact le_refl _

/-! ## Arity four -/

theorem max_four_eq (x : Fin 4 → ℝ) :
    MAX 4 x = max (max (x 0) (x 1)) (max (x 2) (x 3)) := by
  apply le_antisymm
  · refine MAX_le fun i => ?_
    fin_cases i
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  · exact max_le (max_le (le_MAX 4 x 0) (le_MAX 4 x 1)) (max_le (le_MAX 4 x 2) (le_MAX 4 x 3))

set_option maxHeartbeats 8000000 in
/-- The four-input identity, proved on all of `ℝ⁴` by exhaustive case
analysis of the activation pattern. -/
theorem max_four_identity (x : Fin 4 → ℝ) :
    MAX 4 x = x 1 - relu (x 0 - x 2)
      - relu (x 1 + x 2 - x 0 - x 3 + relu (x 0 - x 1))
      + relu (x 1 + x 2 - x 0 - x 3 + relu (x 0 - x 1) + relu (x 0 - x 2))
      + relu (x 3 - x 1 + relu (x 0 - x 2) + relu (x 2 - x 3)) := by
  rw [max_four_eq]
  unfold relu
  simp only [max_def]
  split_ifs <;> linarith

noncomputable def keyA : RealKey 3 := (lbl 1 0 + lbl 2 3, {lbl 0 1})
noncomputable def keyB : RealKey 3 := (lbl 1 0 + lbl 2 3, {lbl 0 1, lbl 0 2})
noncomputable def keyC : RealKey 3 := (lbl 3 1, {lbl 0 2, lbl 2 3})

theorem lbl01_ne_lbl02 : lbl (0 : Fin 4) 1 ≠ lbl 0 2 :=
  lbl_ne ramp (by simp (config := {decide := true}) [ramp])

theorem lbl02_ne_lbl23 : lbl (0 : Fin 4) 2 ≠ lbl 2 3 :=
  lbl_ne ramp (by simp (config := {decide := true}) [ramp]; norm_num)

theorem dot_head_AB (x : Fin 4 → ℝ) :
    dot (lbl 1 0 + lbl 2 3) ((CoordAux.coordT 3).mulVec x) = x 1 + x 2 - x 0 - x 3 := by
  rw [SupportCut.dot_add_left, dot_lbl, dot_lbl]
  ring

theorem realUnitY_keyA (x : Fin 4 → ℝ) :
    realUnitY keyA x = relu (x 1 + x 2 - x 0 - x 3 + relu (x 0 - x 1)) := by
  rw [realUnitY_eq_relu]
  unfold realUnitArg keyA
  rw [Finset.sum_singleton, dot_head_AB, dot_lbl]
  rfl

theorem realUnitY_keyB (x : Fin 4 → ℝ) :
    realUnitY keyB x =
      relu (x 1 + x 2 - x 0 - x 3 + relu (x 0 - x 1) + relu (x 0 - x 2)) := by
  rw [realUnitY_eq_relu]
  unfold realUnitArg keyB
  rw [Finset.sum_pair lbl01_ne_lbl02, dot_head_AB, dot_lbl, dot_lbl, add_assoc]
  rfl

theorem realUnitY_keyC (x : Fin 4 → ℝ) :
    realUnitY keyC x = relu (x 3 - x 1 + relu (x 0 - x 2) + relu (x 2 - x 3)) := by
  rw [realUnitY_eq_relu]
  unfold realUnitArg keyC
  rw [Finset.sum_pair lbl02_ne_lbl23, dot_lbl, dot_lbl, dot_lbl, add_assoc]
  rfl

theorem keyA_ne_keyB : keyA ≠ keyB := by
  intro h
  have h2 := congrArg (fun k : RealKey 3 => k.2.card) h
  simp only [keyA, keyB, Finset.card_singleton, Finset.card_doubleton lbl01_ne_lbl02] at h2
  exact absurd h2 (by norm_num)

theorem keyA_ne_keyC : keyA ≠ keyC := by
  intro h
  have h1 := congrArg (fun k : RealKey 3 => dot k.1 ((CoordAux.coordT 3).mulVec ramp)) h
  simp only [keyA, keyC, dot_head_AB, dot_lbl] at h1
  simp (config := {decide := true}) [ramp] at h1
  norm_num at h1

theorem keyB_ne_keyC : keyB ≠ keyC := by
  intro h
  have h1 := congrArg (fun k : RealKey 3 => dot k.1 ((CoordAux.coordT 3).mulVec ramp)) h
  simp only [keyB, keyC, dot_head_AB, dot_lbl] at h1
  simp (config := {decide := true}) [ramp] at h1
  norm_num at h1

theorem labels_four : ∀ k ∈ ({keyA, keyB, keyC} : Finset (RealKey 3)), ∀ v ∈ k.2,
    IsSimplexDifference v := by
  intro k hk v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;>
    simp only [keyA, keyB, keyC, Finset.mem_insert, Finset.mem_singleton] at hv <;>
    rcases hv with rfl | rfl <;> exact lbl_simplexDifference _ _

/-- **Arity four.** Widths `(11, 5)`, rational weights,
zero biases. -/
theorem max_four_network :
    ∃ net : Network 4 (firstWidth 4) 5,
      (∀ x, net.eval x = Maximum 4 x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  let d : RealKey 3 → ℝ := fun k => if k = keyA then -1 else 1
  apply compile_expansion_width (n := 3) {keyA, keyB, keyC} d
    (coordCoef 1 - hingeCoeff 0 2) labels_four
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (ratVec_lbl 1 0).add (ratVec_lbl 2 3)
    · exact (ratVec_lbl 1 0).add (ratVec_lbl 2 3)
    · exact ratVec_lbl 3 1
  · intro k _
    simp only [d]
    split_ifs
    · exact Subfield.neg_mem _ (Subfield.one_mem _)
    · exact Subfield.one_mem _
  · exact (ratVec_coordCoef 1).sub (ratVec_hingeCoeff 0 2)
  · intro x
    have h : auxiliary (coordCoef 1 - hingeCoeff 0 2) x = x 1 - relu (x 0 - x 2) := by
      unfold auxiliary
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sum_coordCoef, coordLin_feat, sum_hingeCoeff]
      rfl
    have hA : keyA ∉ ({keyB, keyC} : Finset (RealKey 3)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim keyA_ne_keyB keyA_ne_keyC
    have hB : keyB ∉ ({keyC} : Finset (RealKey 3)) := by
      simp only [Finset.mem_singleton]
      exact keyB_ne_keyC
    rw [Finset.sum_insert hA, Finset.sum_insert hB, Finset.sum_singleton, h,
      realUnitY_keyA, realUnitY_keyB, realUnitY_keyC]
    simp only [d, if_pos rfl, if_neg keyA_ne_keyB.symm, if_neg keyA_ne_keyC.symm]
    refine (max_four_identity x).trans ?_
    ring
  · refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 2) ?_
    refine le_trans (Nat.add_le_add_right
      (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 2) ?_
    rw [Finset.card_singleton]

end MaxCaterpillar
