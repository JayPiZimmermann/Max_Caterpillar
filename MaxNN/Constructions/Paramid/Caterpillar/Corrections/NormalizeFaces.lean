import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Normalize

/-! # Orient full cones before generating their faces -/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom MaxNN.Width

variable {n r : ℕ}

theorem normalized_faceKey_mem (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ))
    (hV : ∀ v ∈ V, ∀ z ∈ V, v ≠ -z) (τ : V → Fin 3) :
    normalizedKey (faceKey γ V τ) ∈
      faceKeys (normalizedKey (γ, V)).1 (normalizedKey (γ, V)).2 := by
  classical
  let Q := V.filter fun v => if reverseLabel v then keyExt V τ v = 0 else keyExt V τ v = 1
  let Z := V.filter fun v => keyExt V τ v = 2
  have hQV : Q ⊆ V := Finset.filter_subset _ _
  have hZV : Z ⊆ V := Finset.filter_subset _ _
  have hQZ : Disjoint Q Z := by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    have hq := (Finset.mem_filter.mp hv).2
    have hzz := (Finset.mem_filter.mp hz).2
    rw [hzz] at hq
    split_ifs at hq <;> norm_num [Fin.ext_iff] at hq
  have hPZ : Disjoint (Q.image orientedLabel) (Z.image orientedLabel) := by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hv
    obtain ⟨z, hz, hze⟩ := Finset.mem_image.mp hz
    have he := orientedLabel_injOn hV (hQV hq) (hZV hz) (hqe.trans hze.symm)
    subst z
    exact Finset.disjoint_left.mp hQZ hq hz
  have hγ : (faceKey γ V τ).1 +
      ∑ v in (faceKey γ V τ).2.filter reverseLabel, v =
      (normalizedKey (γ, V)).1 + ∑ v in Q.image orientedLabel, v := by
    change (γ + ∑ v in V.filter (fun v => keyExt V τ v = 1), v) +
      ∑ v in (V.filter (fun v => keyExt V τ v = 2)).filter reverseLabel, v =
      (γ + ∑ v in V.filter reverseLabel, v) + ∑ v in Q.image orientedLabel, v
    rw [Finset.sum_image]
    · simp only [Q, Finset.filter_filter, Finset.sum_filter]
      rw [add_assoc, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v _hv
      unfold orientedLabel
      by_cases hrev : reverseLabel v
      · generalize keyExt V τ v = t
        fin_cases t <;> simp [hrev, Fin.ext_iff]
      · simp [hrev]
    · intro v hv z hz he
      exact orientedLabel_injOn hV (hQV hv) (hQV hz) he
  have hmem := mem_faceKeys_of_disjoint
    (γ := (normalizedKey (γ, V)).1)
    (Finset.image_subset_image hQV) (Finset.image_subset_image hZV) hPZ
  have he : normalizedKey (faceKey γ V τ) =
      ((normalizedKey (γ, V)).1 + ∑ v in Q.image orientedLabel, v,
        Z.image orientedLabel) := by
    apply Prod.ext
    · exact hγ
    · rfl
  rw [he]
  exact hmem

noncomputable def normalizedWordCones (r : ℕ) : Finset (RealKey (r + 1)) :=
  (wordCones r).image normalizedKey

noncomputable def normalizedConeFaceKeys (r : ℕ) : Finset (RealKey (r + 1)) :=
  (normalizedWordCones r).biUnion fun k => faceKeys k.1 k.2

theorem normalizedKeys_subset_coneFaceKeys :
    normalizedKeys r ⊆ normalizedConeFaceKeys r := by
  intro k hk
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨c, hc, hcq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hcq
  apply Finset.mem_biUnion.mpr
  refine ⟨normalizedKey (wordKey w), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨wordKey w, wordKey_mem_wordCones w, rfl⟩
  · exact normalized_faceKey_mem (wordGamma w) (wordLabels w)
      (fun _ hv _ hz => wordLabels_ne_neg w hv hz) τ

theorem normalizedWordCone_labels_card {k : RealKey (r + 1)}
    (hk : k ∈ normalizedWordCones r) : k.2.card = r := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hq
  change ((wordLabels w).image orientedLabel).card = r
  rw [Finset.card_image_iff.mpr
    (orientedLabel_injOn (fun _ hv _ hz => wordLabels_ne_neg w hv hz))]
  exact wordLabels_card w

/-- The face bound is charged only once for every full cone after orientation
normalization. This precedes both face-key deduplication and coefficient pruning. -/
theorem card_normalizedKeys_le_normalizedWordCones :
    (normalizedKeys r).card ≤ (normalizedWordCones r).card * 3 ^ r := by
  refine (Finset.card_le_of_subset normalizedKeys_subset_coneFaceKeys).trans ?_
  unfold normalizedConeFaceKeys
  refine Finset.card_biUnion_le.trans ?_
  calc
    ∑ k in normalizedWordCones r, (faceKeys k.1 k.2).card ≤
        ∑ _k in normalizedWordCones r, 3 ^ r := Finset.sum_le_sum fun k hk => by
          simpa only [normalizedWordCone_labels_card hk] using card_faceKeys_le k.1 k.2
    _ = (normalizedWordCones r).card * 3 ^ r := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]

theorem card_normalizedWordCones_le :
    (normalizedWordCones r).card ≤ (wordCones r).card := Finset.card_image_le

theorem CorrectionTable.twoLayerWidth_normalizedCone_bound (T : CorrectionTable r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1))
      ((normalizedWordCones r).card * 3 ^ r + 2) (MAX (r + 1 + 1)) :=
  T.twoLayerWidth_normalized.mono_right
    (Nat.add_le_add_right card_normalizedKeys_le_normalizedWordCones 2)

theorem twoLayerWidth_MAX_normalizedCone_bound (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1))
      ((normalizedWordCones r).card * 3 ^ r + 2) (MAX (r + 1 + 1)) := by
  obtain ⟨T⟩ := exists_correctionTable_of_formulaClassIdentity hr hclass
  exact T.twoLayerWidth_normalizedCone_bound

end MaxNN.Caterpillar.Corrections
