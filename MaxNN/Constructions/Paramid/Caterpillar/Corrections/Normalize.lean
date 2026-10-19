import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Table

/-! # Merging correction units after orienting their labels

Reversing a label `v` and adding `v` to the linear preactivation leaves the
unit unchanged. Orienting every simplex difference by its vertex indices
therefore gives a further exact quotient of the finite correction dictionary.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidChain MaxNN.Width

variable {n r : ℕ}

def reverseLabel (v : Fin n → ℝ) : Prop :=
  ∃ a b : Fin (n + 1), b < a ∧ v = toR (vtx a) - toR (vtx b)

noncomputable def orientedLabel (v : Fin n → ℝ) : Fin n → ℝ :=
  by classical exact if reverseLabel v then -v else v

noncomputable def normalizedKey (k : RealKey n) : RealKey n :=
  by classical exact (k.1 + ∑ v in k.2.filter reverseLabel, v, k.2.image orientedLabel)

theorem wordLabels_ne_neg (w : WordIndex r) {v z : Fin (r + 1) → ℝ}
    (hv : v ∈ wordLabels w) (hz : z ∈ wordLabels w) : v ≠ -z := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
  intro he
  have hne : w.1 (parent w.2.1 j.succ).succ ≠ w.1 j.succ.succ := by
    intro h
    have hh := Fin.succ_injective _ (w.1.injective h)
    exact (ne_of_lt (parent_lt (Fin.succ_pos j))) hh
  have he' : toR (vtx (w.1 (parent w.2.1 j.succ).succ)) -
      toR (vtx (w.1 j.succ.succ)) =
      toR (vtx (w.1 k.succ.succ)) - toR (vtx (w.1 (parent w.2.1 k.succ).succ)) := by
    simpa only [edgeVecs, wordBase, neg_sub] using he
  have hp := simplex_difference_endpoints hne he'
  have hj := Fin.succ_injective _ (w.1.injective hp.1)
  have hk := Fin.succ_injective _ (w.1.injective hp.2)
  have hlt := parent_lt (S := w.2.1) (Fin.succ_pos j)
  rw [hj, hk] at hlt
  exact (not_lt_of_ge (le_of_lt (parent_lt (S := w.2.1) (Fin.succ_pos k)))) hlt

theorem correctionKey_labels_ne_neg {k : RealKey (r + 1)} (hk : k ∈ correctionKeys r)
    {v z : Fin (r + 1) → ℝ} (hv : v ∈ k.2) (hz : z ∈ k.2) : v ≠ -z := by
  obtain ⟨q, hq, hqk⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hqk
  apply wordLabels_ne_neg w
  · exact Finset.mem_of_mem_filter v hv
  · exact Finset.mem_of_mem_filter z hz

theorem orientedLabel_injOn {V : Finset (Fin n → ℝ)}
    (hV : ∀ v ∈ V, ∀ z ∈ V, v ≠ -z) : Set.InjOn orientedLabel (V : Set (Fin n → ℝ)) := by
  intro v hv z hz he
  unfold orientedLabel at he
  split_ifs at he with hvf hzf hzf
  · exact neg_injective he
  · exact False.elim (hV v hv z hz (neg_eq_iff_eq_neg.mp he))
  · exact False.elim (hV v hv z hz he)
  · exact he

theorem paramidOn_normalizedKey (k : RealKey n)
    (hV : ∀ v ∈ k.2, ∀ z ∈ k.2, v ≠ -z) :
    paramidOn (normalizedKey k).1 (normalizedKey k).2 = paramidOn k.1 k.2 := by
  classical
  funext y
  unfold paramidOn normalizedKey
  congr 1
  rw [SupportCut.dot_add_left, Finset.sum_image]
  · have hdot : dot (∑ v in k.2.filter reverseLabel, v) y =
        ∑ v in k.2.filter reverseLabel, dot v y := by
      simp only [dot, Finset.sum_apply, Finset.sum_mul]
      exact Finset.sum_comm
    rw [hdot, Finset.sum_filter]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro v _hv
    unfold orientedLabel
    by_cases h : reverseLabel v
    · simp only [if_pos h, FlagAux.dot_neg_left]
      linarith [relu_sub_relu_neg (dot v y)]
    · simp only [if_neg h, zero_add]
  · exact orientedLabel_injOn hV

theorem orientedLabel_simplexDifference {v : Fin n → ℝ} (hv : IsSimplexDifference v) :
    IsSimplexDifference (orientedLabel v) := by
  classical
  unfold orientedLabel
  split_ifs
  · obtain ⟨a, b, rfl⟩ := hv
    exact ⟨b, a, neg_sub _ _⟩
  · exact hv

noncomputable def normalizedKeys (r : ℕ) : Finset (RealKey (r + 1)) :=
  (correctionKeys r).image normalizedKey

theorem card_normalizedKeys_le (r : ℕ) :
    (normalizedKeys r).card ≤ (correctionKeys r).card := Finset.card_image_le

theorem normalizedKeys_simplexDifference :
    ∀ k ∈ normalizedKeys r, ∀ v ∈ k.2, IsSimplexDifference v := by
  intro k hk v hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  exact orientedLabel_simplexDifference (correctionKeys_simplexDifference q hq z hz)

theorem realUnitY_normalizedKey {k : RealKey (r + 1)} (hk : k ∈ correctionKeys r) :
    realUnitY (normalizedKey k) = realUnitY k := by
  funext y
  exact congrFun (paramidOn_normalizedKey k
    (fun _ hv _ hz => correctionKey_labels_ne_neg hk hv hz)) _

theorem realUnitSpan_le_normalized :
    RealUnitSpan (r + 1) (correctionKeys r) ≤
      RealUnitSpan (r + 1) (normalizedKeys r) := by
  intro f hf
  obtain ⟨c, q, hq, he⟩ := hf
  have he' : f = (∑ k in correctionKeys r, c k • realUnitY k) + q := by
    funext y
    simpa only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using he y
  rw [he']
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k hk => ?_)
    (pairLin_mem_realUnitSpan hq)
  apply Submodule.smul_mem
  rw [← realUnitY_normalizedKey hk]
  exact realUnitY_mem_realUnitSpan (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem CorrectionTable.twoLayerWidth_normalized (T : CorrectionTable r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1)) ((normalizedKeys r).card + 2)
      (MAX (r + 1 + 1)) :=
  twoLayerWidth_of_mem_realUnitSpan normalizedKeys_simplexDifference
    (realUnitSpan_le_normalized ⟨T.coeff, T.remainder, T.remainder_pairLin, T.computes⟩)

/-- The normalized output row is the sum of the original coefficients in
each fiber; it does not select a representation of the target function. -/
noncomputable def CorrectionTable.normalizedCoeff (T : CorrectionTable r)
    (k : RealKey (r + 1)) : ℝ := by
  classical
  exact ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k), T.coeff q

theorem CorrectionTable.sum_normalizedCoeff (T : CorrectionTable r)
    (y : Fin (r + 1 + 1) → ℝ) :
    ∑ k in normalizedKeys r, T.normalizedCoeff k * realUnitY k y =
      ∑ k in correctionKeys r, T.coeff k * realUnitY k y := by
  classical
  unfold CorrectionTable.normalizedCoeff
  simp only [Finset.sum_mul]
  calc
    ∑ k in normalizedKeys r,
        ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k),
          T.coeff q * realUnitY k y =
      ∑ k in normalizedKeys r,
        ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k),
          T.coeff q * realUnitY q y := by
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro q hq
            obtain ⟨hq, hqk⟩ := Finset.mem_filter.mp hq
            rw [← hqk, realUnitY_normalizedKey hq]
    _ = ∑ q in correctionKeys r, T.coeff q * realUnitY q y :=
      Finset.sum_fiberwise_of_maps_to
        (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩) _

noncomputable def CorrectionTable.normalizedActiveKeys (T : CorrectionTable r) :
    Finset (RealKey (r + 1)) := by
  classical
  exact (normalizedKeys r).filter (fun k => T.normalizedCoeff k ≠ 0)

theorem CorrectionTable.card_normalizedActiveKeys_le (T : CorrectionTable r) :
    T.normalizedActiveKeys.card ≤ (normalizedKeys r).card :=
  Finset.card_le_of_subset (Finset.filter_subset _ _)

theorem CorrectionTable.computes_normalizedActive (T : CorrectionTable r)
    (y : Fin (r + 1 + 1) → ℝ) :
    MAX (r + 1 + 1) y =
      ∑ k in T.normalizedActiveKeys, T.normalizedCoeff k * realUnitY k y + T.remainder y := by
  rw [T.computes y, ← T.sum_normalizedCoeff y]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hka
  have hzero : T.normalizedCoeff k = 0 := by
    by_contra hn
    exact hka (Finset.mem_filter.mpr ⟨hk, hn⟩)
  rw [hzero, zero_mul]

/-- Orient and merge all labels, sum their output coefficients, and finally
remove every fiber whose total coefficient cancels. -/
theorem CorrectionTable.twoLayerWidth_normalizedActive (T : CorrectionTable r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1)) (T.normalizedActiveKeys.card + 2)
      (MAX (r + 1 + 1)) := by
  apply twoLayerWidth_of_mem_realUnitSpan
  · intro k hk
    exact normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  · exact ⟨T.normalizedCoeff, T.remainder, T.remainder_pairLin, T.computes_normalizedActive⟩

end MaxNN.Caterpillar.Corrections
