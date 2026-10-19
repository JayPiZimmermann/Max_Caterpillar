import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Span
import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex
import MaxNN.Constructions.Paramid.Geom.Faces.ConeOnly

/-!
# The finite correction dictionary of the caterpillar formula

This file turns the class identity for the explicit caterpillar sum into an
ordinary two-hidden-layer network.  The correction dictionary is a single
finite union of all cone-face keys; no recursive network occurs in its
definition.  Full dimensionality and the class identity are kept as named
hypotheses here and are discharged separately.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidGeom.Faces MaxNN.Width MaxNN.ParamidChain

variable {r : ℕ}

/-- One occurrence of a decorated caterpillar word in the explicit formula. -/
abbrev WordIndex (r : ℕ) :=
  Equiv.Perm (Fin (r + 1 + 1)) × ↑(admissibleCuts r)

noncomputable def wordApex (w : WordIndex r) : Fin (r + 1) → ℝ :=
  toR (vtx (w.1 0))

noncomputable def wordBase (w : WordIndex r) : Fin (r + 1) → Fin (r + 1) → ℝ :=
  fun i => toR (vtx (w.1 i.succ))

noncomputable def wordGamma (w : WordIndex r) : Fin (r + 1) → ℝ :=
  wordBase w (lastHead w.2.1) - wordApex w

noncomputable def wordLabels (w : WordIndex r) : Finset (Fin (r + 1) → ℝ) :=
  Finset.univ.image (edgeVecs (wordBase w) w.2.1)

noncomputable def wordKey (w : WordIndex r) : RealKey (r + 1) :=
  (wordGamma w, wordLabels w)

/-- The distinct full-dimensional word cones; repeated decorated words are
identified before any face keys are generated. -/
noncomputable def wordCones (r : ℕ) : Finset (RealKey (r + 1)) :=
  Finset.univ.image wordKey

/-- The deduplicated dictionary of every cone-face correction of every word. -/
noncomputable def correctionKeys (r : ℕ) : Finset (RealKey (r + 1)) :=
  (wordCones r).biUnion fun k => faceKeys k.1 k.2

theorem wordKey_mem_wordCones (w : WordIndex r) : wordKey w ∈ wordCones r :=
  Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩

theorem faceKeys_subset_correctionKeys (w : WordIndex r) :
    faceKeys (wordGamma w) (wordLabels w) ⊆ correctionKeys r :=
  Finset.subset_biUnion_of_mem (fun k : RealKey (r + 1) => faceKeys k.1 k.2)
    (wordKey_mem_wordCones w)

theorem wordLabels_card (w : WordIndex r) : (wordLabels w).card = r := by
  unfold wordLabels wordBase
  rw [Finset.card_image_of_injective _]
  · rw [Finset.card_univ, Fintype.card_fin]
  · exact edgeVecs_simplex_injective (fun i => w.1 i.succ)
      (w.1.injective.comp (Fin.succ_injective (r + 1))) w.2.1

theorem card_wordCones_le : (wordCones r).card ≤ Fintype.card (WordIndex r) := by
  unfold wordCones
  simpa only [Finset.card_univ] using Finset.card_image_le (s := Finset.univ) (f := wordKey)

/-- Face expansion is applied only after equal word cones have been merged. -/
theorem card_correctionKeys_le_distinct :
    (correctionKeys r).card ≤ (wordCones r).card * 3 ^ r := by
  unfold correctionKeys
  refine Finset.card_biUnion_le.trans ?_
  calc
    ∑ k in wordCones r, (faceKeys k.1 k.2).card
        ≤ ∑ _k in wordCones r, 3 ^ r := Finset.sum_le_sum fun k hk => by
          obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hk
          calc
            (faceKeys (wordGamma w) (wordLabels w)).card ≤
                3 ^ (wordLabels w).card := card_faceKeys_le _ _
            _ = 3 ^ r := by rw [wordLabels_card]
    _ = (wordCones r).card * 3 ^ r := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]

/-- A raw but fully symbolic count: deduplication can only reduce the union. -/
theorem card_correctionKeys_le :
    (correctionKeys r).card ≤ Fintype.card (WordIndex r) * 3 ^ r := by
  exact card_correctionKeys_le_distinct.trans
    (Nat.mul_le_mul_right (3 ^ r) card_wordCones_le)

theorem wordLabels_simplexDifference (w : WordIndex r) :
    ∀ v ∈ wordLabels w, IsSimplexDifference v := by
  intro v hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨w.1 (parent (r := r) w.2.1 j.succ).succ, w.1 j.succ.succ, ?_⟩
  simp only [edgeVecs, wordBase]

theorem correctionKeys_simplexDifference :
    ∀ k ∈ correctionKeys r, ∀ v ∈ k.2, IsSimplexDifference v := by
  intro k hk v hv
  obtain ⟨k, hk, hkk⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hkk
  unfold faceKey at hv
  exact wordLabels_simplexDifference w v (Finset.mem_of_mem_filter v hv)

/-- The paramid part of one word, with its linear apex removed. -/
noncomputable def wordCone (w : WordIndex r) : (Fin (r + 1) → ℝ) → ℝ :=
  paramidOn (wordGamma w) (wordLabels w)

noncomputable def wordCoeff (w : WordIndex r) : ℝ :=
  wordWeight r w.2.1

noncomputable def rawApex (π : Equiv.Perm (Fin (r + 1 + 1))) : Fin (r + 1) → ℝ :=
  toR (vtx (π 0))

noncomputable def rawBase (π : Equiv.Perm (Fin (r + 1 + 1))) :
    Fin (r + 1) → Fin (r + 1) → ℝ :=
  fun i => toR (vtx (π i.succ))

noncomputable def rawGamma (π : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1))) : Fin (r + 1) → ℝ :=
  rawBase π (lastHead S) - rawApex π

noncomputable def rawLabels (π : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1))) : Finset (Fin (r + 1) → ℝ) :=
  Finset.univ.image (edgeVecs (rawBase π) S)

noncomputable def rawCone (π : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1))) : (Fin (r + 1) → ℝ) → ℝ :=
  paramidOn (rawGamma π S) (rawLabels π S)

theorem wordData_eq_raw (w : WordIndex r) :
    wordApex w = rawApex w.1 ∧ wordBase w = rawBase w.1 ∧
      wordGamma w = rawGamma w.1 w.2.1 ∧ wordLabels w = rawLabels w.1 w.2.1 ∧
      wordCone w = rawCone w.1 w.2.1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The explicit cone sum used by Theorem F. -/
noncomputable def coneFormula (r : ℕ) : (Fin (r + 1) → ℝ) → ℝ :=
  fun y => ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
    wordWeight r S * rawCone π S y

theorem word_caterpillar_eq_linear_add_cone (w : WordIndex r) :
    caterpillarUnit (wordApex w) (wordBase w) w.2.1 =
      dot (wordApex w) + wordCone w := by
  unfold wordCone wordGamma wordLabels
  rw [caterpillarUnit_eq_dot_add_paramidOn]
  exact edgeVecs_simplex_injective (fun i => w.1 i.succ)
    (w.1.injective.comp (Fin.succ_injective (r + 1))) w.2.1

/-- The difference between the original decorated-word formula and its cone
sum is an explicit linear function. -/
theorem formula_eq_coneFormula_add_linear :
    formula r = coneFormula r + fun y =>
      ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
        wordWeight r S * dot (rawApex π) y := by
  rw [formula_eq_sum]
  funext y
  unfold coneFormula
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro π _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hw := congrFun (word_caterpillar_eq_linear_add_cone
    (r := r) (π, ⟨S, hS⟩)) y
  change caterpillarUnit (toR (vtx (π 0))) (fun i => toR (vtx (π i.succ))) S y =
    dot (rawApex π) y + rawCone π S y at hw
  rw [hw]
  change wordWeight r S * (dot (rawApex π) y + rawCone π S y) = _
  ring

/-- The geometric hypotheses needed to invoke Theorem F on the actual word
cones. -/
def FullDimensionalWords (r : ℕ) : Prop :=
  ∀ w : WordIndex r, FiniteDimensional.finrank ℝ
    (vectorSpan ℝ (coneVertsOn (wordGamma w) (wordLabels w) : Set (Fin (r + 1) → ℝ))) = r + 1

/-- The all-arity class identity needed from the facet proof. -/
def CaterpillarClassIdentity (r : ℕ) : Prop :=
  coneFormula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r

/-- Under the checked geometric class identity, the simplex support function
belongs to the one finite correction dictionary. -/
theorem simplex_mem_correctionSpan (hr : 1 ≤ r) (hfull : FullDimensionalWords r)
    (hclass : CaterpillarClassIdentity r) :
    hS (simplexVerts (r + 1)) ∈
      (RealUnitSpan (r + 1) (correctionKeys r)).comap (MaxNN.Width.coordPull (r + 1)) := by
  let I := Equiv.Perm (Fin (r + 1 + 1)) × Finset (Fin (r + 1))
  let s : Finset I := Finset.univ.product (admissibleCuts r)
  let a : I → ℝ := fun w => wordWeight r w.2
  let γ : I → Fin (r + 1) → ℝ := fun w => rawGamma w.1 w.2
  let V : I → Finset (Fin (r + 1) → ℝ) := fun w => rawLabels w.1 w.2
  have hsum : (fun y => ∑ w in s, a w * paramidOn (γ w) (V w) y) = coneFormula r := by
    funext y
    change (∑ w in Finset.univ.product (admissibleCuts r),
      wordWeight r w.2 * paramidOn (rawGamma w.1 w.2) (rawLabels w.1 w.2) y) =
      ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
        wordWeight r S * rawCone π S y
    exact Finset.sum_product
  have hF := simplex_sub_mem_coneFaceSpan (n := r + 1) (by omega) s a γ V
    (fun w hw => by
      have hS : w.2 ∈ admissibleCuts r := (Finset.mem_product.mp hw).2
      exact hfull (w.1, ⟨w.2, hS⟩)) (by
      change (fun y => ∑ w in s, a w * paramidOn (γ w) (V w) y) -
        hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) (r + 1 - 1)
      rw [hsum, Nat.add_sub_cancel]
      exact hclass)
  have hF' : hS (simplexVerts (r + 1)) - coneFormula r ∈
      Submodule.span ℝ {f | ∃ w ∈ s, ∃ F ∈ coneFamily (γ w) (V w),
        F ≠ coneVertsOn (γ w) (V w) ∧ F.Nonempty ∧ f = hS F} ⊔ LSpan (r + 1) 0 := by
    rw [← hsum]
    exact hF
  have hproper : Submodule.span ℝ {f | ∃ w ∈ s, ∃ F ∈ coneFamily (γ w) (V w),
      F ≠ coneVertsOn (γ w) (V w) ∧ F.Nonempty ∧ f = hS F} ≤
      (RealUnitSpan (r + 1) (correctionKeys r)).comap (MaxNN.Width.coordPull (r + 1)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, hw, F, hmem, -, -, rfl⟩
    have hS : w.2 ∈ admissibleCuts r := (Finset.mem_product.mp hw).2
    let w' : WordIndex r := (w.1, ⟨w.2, hS⟩)
    exact hS_coord_mem_realUnitSpan_of_mem_coneFamily
      (faceKeys_subset_correctionKeys w') (wordLabels_simplexDifference w') hmem
  have hlin : LSpan (r + 1) 0 ≤
      (RealUnitSpan (r + 1) (correctionKeys r)).comap (MaxNN.Width.coordPull (r + 1)) := by
    rw [Faces.LSpan_zero_eq, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact pairLin_mem_realUnitSpan (MaxNN.Width.dot_coordT_mem_pairLin (r + 1) p)
  have hcorr := sup_le hproper hlin hF'
  have hcones : coneFormula r ∈
      (RealUnitSpan (r + 1) (correctionKeys r)).comap (MaxNN.Width.coordPull (r + 1)) := by
    have he : coneFormula r = ∑ π : Equiv.Perm (Fin (r + 1 + 1)),
        ∑ S in admissibleCuts r, wordWeight r S • rawCone π S := by
      funext y
      simp only [coneFormula, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [he]
    exact Submodule.sum_mem _ fun π _ => Submodule.sum_mem _ fun S hS =>
      Submodule.smul_mem _ _ (realUnitY_mem_realUnitSpan
        (faceKeys_subset_correctionKeys (π, ⟨S, hS⟩) (self_mem_faceKeys _ _)))
  have he : hS (simplexVerts (r + 1)) =
      (hS (simplexVerts (r + 1)) - coneFormula r) + coneFormula r := by
    abel
  rw [he]
  exact Submodule.add_mem _ hcorr hcones

/-- The actual ordinary two-hidden-layer network obtained from the
caterpillar cones and all their proper-face corrections. -/
theorem twoLayerWidth_MAX_of_classIdentity (hr : 1 ≤ r)
    (hfull : FullDimensionalWords r) (hclass : CaterpillarClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1)) ((correctionKeys r).card + 2)
      (MAX (r + 1 + 1)) := by
  have hΔ := simplex_mem_correctionSpan hr hfull hclass
  have hmax : MAX (r + 1 + 1) ∈ RealUnitSpan (r + 1) (correctionKeys r) := by
    have he : MAX (r + 1 + 1) = (fun y => y 0) +
        MaxNN.Width.coordPull (r + 1) (hS (simplexVerts (r + 1))) := by
      funext y
      exact CoordAux.MAX_succ_eq_add_hS_simplexVerts y
    rw [he]
    exact Submodule.add_mem _ (pairLin_mem_realUnitSpan (coord_mem_pairLin 0))
      (Submodule.mem_comap.mp hΔ)
  exact twoLayerWidth_of_mem_realUnitSpan correctionKeys_simplexDifference hmax

end MaxNN.Caterpillar.Corrections
