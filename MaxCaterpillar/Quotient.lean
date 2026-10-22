import MaxCaterpillar.Theorems

/-! # Quotient-basis compression (Version 2 width)

Let `V_N` be the span of the dictionary and `A_N ⊆ V_N` the span of the
auxiliary functions `σ(x_i)`, `σ(-x_i)`, `σ(x_i - x_j)`.  Put
`q_N = dim (V_N / A_N)`.  Extending a basis of `A_N` drawn from the auxiliary
functions to a basis of `V_N` drawn from the dictionary adds exactly `q_N`
functions.  One normalized description is selected for each added face
function; the maximum is then an expansion by at most `q_N` units plus an
auxiliary remainder, with rational coefficients, and compiles with the same
first hidden layer and `q_N + 2` second-layer neurons.

The Version 1 width `secondWidth` is retained; this file adds a second bound.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom

/-- The auxiliary span `A_N`. -/
noncomputable def auxSpan (N : ℕ) : Submodule ℝ (Point N → ℝ) :=
  Submodule.span ℝ (Set.range fun j : Fin (W N) => fun x : Point N => feat N x j)

/-- The span `V_N` of the dictionary. -/
noncomputable def vocabularySpan (r : ℕ) : Submodule ℝ (Point (r + 1 + 1) → ℝ) :=
  Submodule.span ℝ (↑(dictionary r) : Set (Point (r + 1 + 1) → ℝ))

noncomputable instance (r : ℕ) : FiniteDimensional ℝ (vocabularySpan r) :=
  FiniteDimensional.span_finset ℝ _

theorem auxSpan_le_vocabularySpan (r : ℕ) : auxSpan (r + 1 + 1) ≤ vocabularySpan r := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  rw [dictionary_eq_range]
  exact ⟨Sum.inr j, rfl⟩

/-- `q_N = dim (V_N / A_N)` for `N = r + 2`. -/
noncomputable def quotientDim (r : ℕ) : ℕ :=
  FiniteDimensional.finrank ℝ (↥(vocabularySpan r) ⧸
    (auxSpan (r + 1 + 1)).comap (vocabularySpan r).subtype)

theorem quotientDim_eq (r : ℕ) : quotientDim r =
    FiniteDimensional.finrank ℝ (vocabularySpan r) - FiniteDimensional.finrank ℝ (auxSpan (r + 1 + 1)) := by
  have h := Submodule.finrank_quotient_add_finrank
    ((auxSpan (r + 1 + 1)).comap (vocabularySpan r).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (auxSpan_le_vocabularySpan r)).finrank_eq] at h
  unfold quotientDim
  exact (Nat.sub_eq_of_eq_add h.symm).symm

/-- **Quotient-basis compression.** At most `q_N` normalized face functions,
one normalized description each, together with an auxiliary remainder
represent the maximum with rational coefficients; hence a network with the
same first hidden layer, `q_N + 2` second-layer neurons, rational weights,
and zero biases computes it. -/
theorem quotient_compression (r : ℕ) (hr : 1 ≤ r) :
    ∃ K : Finset (RealKey (r + 1)), K ⊆ normalizedKeys r ∧ K.card ≤ quotientDim r ∧
      ∃ net : Network (r + 1 + 1) (firstWidth (r + 1 + 1)) (quotientDim r + 2),
        (∀ x, net.eval x = Maximum (r + 1 + 1) x) ∧ net.HasRationalWeights ∧
          net.HasZeroBiases := by
  classical
  letI : DecidableEq (Point (r + 1 + 1) → ℝ) := Classical.decEq _
  haveI : NeZero (r + 1 + 1) := ⟨by omega⟩
  let F : Set (Point (r + 1 + 1) → ℝ) :=
    Set.range fun j : Fin (W (r + 1 + 1)) => fun x => feat (r + 1 + 1) x j
  let T : Set (Point (r + 1 + 1) → ℝ) := ↑(dictionary r)
  obtain ⟨s, hsF, hspan_s, hli_s⟩ := exists_linearIndependent ℝ F
  have hFT : F ⊆ T := by
    change F ⊆ ↑(dictionary r)
    rw [dictionary_eq_range]
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inr j, rfl⟩
  obtain ⟨b, hbT, hsb, hTb, hli_b⟩ :=
    exists_linearIndependent_extension hli_s (hsF.trans hFT)
  have hbfin : b.Finite := (Finset.finite_toSet (dictionary r)).subset hbT
  have hsfin : s.Finite := hbfin.subset hsb
  haveI : Fintype b := hbfin.fintype
  haveI : Fintype s := hsfin.fintype
  have hVb : Submodule.span ℝ b = vocabularySpan r :=
    le_antisymm (Submodule.span_mono hbT) (Submodule.span_le.mpr hTb)
  have hcardb : FiniteDimensional.finrank ℝ (vocabularySpan r) = b.toFinset.card := by
    rw [← hVb]; exact finrank_span_set_eq_card b hli_b
  have hcards : FiniteDimensional.finrank ℝ (auxSpan (r + 1 + 1)) = s.toFinset.card := by
    have h : Submodule.span ℝ s = auxSpan (r + 1 + 1) := hspan_s
    rw [← h]; exact finrank_span_set_eq_card s hli_s
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Point (r + 1 + 1) → ℝ), J = b.toFinset \ s.toFinset :=
    ⟨_, rfl⟩
  have hJcard : J.card = quotientDim r := by
    rw [hJdef, quotientDim_eq, hcardb, hcards]
    exact Finset.card_sdiff (Set.toFinset_subset_toFinset.mpr hsb)
  -- one normalized description for every selected face function
  let P : (Point (r + 1 + 1) → ℝ) → Prop := fun g => ∃ k ∈ correctionKeys r, realUnitY k = g
  obtain ⟨keyFor, hkeyFor⟩ : ∃ keyFor : (Point (r + 1 + 1) → ℝ) → RealKey (r + 1),
      ∀ g, P g → keyFor g ∈ normalizedKeys r ∧ realUnitY (keyFor g) = g := by
    refine ⟨fun g => if h : P g then normalizedKey (Classical.choose h) else (0, ∅), ?_⟩
    intro g h
    have hs := Classical.choose_spec h
    simp only [dif_pos h]
    exact ⟨Finset.mem_image_of_mem _ hs.1, (realUnitY_normalizedKey hs.1).trans hs.2⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Finset (RealKey (r + 1)), K = (J.filter P).image keyFor :=
    ⟨_, rfl⟩
  have hKsub : K ⊆ normalizedKeys r := by
    intro k hk
    rw [hKdef] at hk
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hk
    exact (hkeyFor g (Finset.mem_filter.mp hg).2).1
  have hKcard : K.card ≤ quotientDim r := by
    rw [hKdef]
    exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hJcard.le
  refine ⟨K, hKsub, hKcard, ?_⟩
  -- the family: selected units, then the auxiliary functions
  let v : (↥K ⊕ Fin (W (r + 1 + 1))) → Point (r + 1 + 1) → ℝ := fun i =>
    match i with
    | Sum.inl k => realUnitY k.1
    | Sum.inr j => fun x => feat (r + 1 + 1) x j
  have hbv : b ⊆ Submodule.span ℝ (Set.range v) := by
    intro g hg
    apply Submodule.subset_span
    by_cases hgs : g ∈ s
    · obtain ⟨j, rfl⟩ := hsF hgs
      exact ⟨Sum.inr j, rfl⟩
    · have hgT : g ∈ T := hbT hg
      change g ∈ (↑(dictionary r) : Set _) at hgT
      rw [dictionary_eq_range] at hgT
      obtain ⟨i, rfl⟩ := hgT
      cases i with
      | inl k =>
          have hP : P (atom r (Sum.inl k)) := ⟨k.1, k.2, rfl⟩
          have hJ : atom r (Sum.inl k) ∈ J.filter P := by
            rw [hJdef]
            refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hP⟩
            · exact Set.mem_toFinset.mpr hg
            · rw [Set.mem_toFinset]; exact hgs
          have hK : keyFor (atom r (Sum.inl k)) ∈ K := by
            rw [hKdef]; exact Finset.mem_image_of_mem _ hJ
          refine ⟨Sum.inl ⟨keyFor (atom r (Sum.inl k)), hK⟩, ?_⟩
          show realUnitY (keyFor (atom r (Sum.inl k))) = atom r (Sum.inl k)
          exact (hkeyFor _ hP).2
      | inr j => exact ⟨Sum.inr j, rfl⟩
  have hmax : MAX (r + 1 + 1) ∈ Submodule.span ℝ (Set.range v) := by
    have h := maximum_mem_dictionary r hr
    change MAX (r + 1 + 1) ∈ vocabularySpan r at h
    rw [← hVb] at h
    exact Submodule.span_le.mpr hbv h
  have hcont : ∀ i, Continuous (v i) := by
    intro i
    cases i with
    | inl k =>
        exact (Canonical.realUnitY_posHomContinuous k.1
          (normalizedKeys_simplexDifference k.1 (hKsub k.2))).1
    | inr j => exact (Canonical.feat_posHomContinuous _ j).1
  have hrat : ∀ i, ∀ y ∈ ratPoints (r + 1 + 1), v i y ∈ ratField := by
    intro i y hy
    cases i with
    | inl k =>
        exact realUnitY_mem_ratField (ratVec_normalizedKey (hKsub k.2))
          (normalizedKeys_simplexDifference k.1 (hKsub k.2)) hy
    | inr j => exact feat_mem_ratField hy j
  obtain ⟨c, hc, hcx⟩ := exists_rat_coeff_of_mem_span v hcont hrat hmax
    (fun y hy => MAX_mem_ratField hy)
  let d : RealKey (r + 1) → ℝ := fun k => if h : k ∈ K then c (Sum.inl ⟨k, h⟩) else 0
  have hexp : ∀ x, MAX (r + 1 + 1) x =
      ∑ k in K, d k * realUnitY k x + auxiliary (fun j => c (Sum.inr j)) x := by
    intro x
    rw [hcx x, Fintype.sum_sum_type]
    congr 1
    rw [← Finset.sum_coe_sort K]
    apply Finset.sum_congr rfl
    intro k _
    show c (Sum.inl k) * v (Sum.inl k) x = d k.1 * realUnitY k.1 x
    rw [show d k.1 = c (Sum.inl k) from dif_pos k.2]
  have hd : ∀ k ∈ K, d k ∈ ratField := by
    intro k hk
    rw [show d k = c (Sum.inl ⟨k, hk⟩) from dif_pos hk]
    exact hc _
  obtain ⟨net, heval, hratw, hzero⟩ := compile_expansion_width K d (fun j => c (Sum.inr j))
    (fun k hk => normalizedKeys_simplexDifference k (hKsub hk))
    (fun k hk => ratVec_normalizedKey (hKsub hk)) hd
    (fun j => hc _) hexp (Nat.add_le_add_right hKcard 2)
  exact ⟨net, heval, hratw, hzero⟩

end MaxCaterpillar
