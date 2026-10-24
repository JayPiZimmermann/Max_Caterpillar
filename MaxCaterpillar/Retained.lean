import MaxCaterpillar.Quotient

/-! # Retained descriptions

The essential normalized descriptions `K` and the auxiliary functions span the
dictionary (`vocabularySpan_le_essential`); hence `q_N ≤ |K|`, and
`q_N + 2` never exceeds `secondWidth N` (`quotientDim_add_two_le_secondWidth`).

The bound `q_N ≤ |essential normalized descriptions|` holds because every
dictionary unit equals the unit of its normalized description, and the
normalized descriptions with no hinges and a coordinate-difference head
(`hingeKeys`) are auxiliary functions.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom

/-- The essential normalized descriptions, as a type. -/
abbrev EssentialKey (r : ℕ) := (↑(essentialKeys (normalizedKeys r)) : Type)

theorem mem_essentialKeys {r : ℕ} {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r)
    (hh : k ∉ hingeKeys (normalizedKeys r)) : k ∈ essentialKeys (normalizedKeys r) := by
  unfold essentialKeys
  exact @Finset.mem_sdiff _ (absorbHingesRealKeyDecidableEq (r + 1)) _ _ _ |>.mpr ⟨hk, hh⟩

/-- The dictionary span is spanned by the essential normalized units together
with the auxiliary functions. -/
theorem vocabularySpan_le_essential (r : ℕ) :
    vocabularySpan r ≤
      Submodule.span ℝ (Set.range fun k : EssentialKey r => realUnitY k.1) ⊔
        auxSpan (r + 1 + 1) := by
  classical
  unfold vocabularySpan
  rw [dictionary_eq_range]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inr j => exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  | inl k =>
    show realUnitY k.1 ∈ _
    have hnk : normalizedKey k.1 ∈ normalizedKeys r := Finset.mem_image_of_mem _ k.2
    rw [← realUnitY_normalizedKey k.2]
    by_cases hh : normalizedKey k.1 ∈ hingeKeys (normalizedKeys r)
    · apply Submodule.mem_sup_right
      have hfun : realUnitY (normalizedKey k.1) =
          ∑ j, rootHingeCoeff (normalizedKey k.1).1 j •
            (fun x : Point (r + 1 + 1) => feat (r + 1 + 1) x j) := by
        funext x
        rw [realUnitY_hingeKey _ hh x, Finset.sum_apply]
        rfl
      rw [hfun]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      exact ⟨⟨normalizedKey k.1, mem_essentialKeys hnk hh⟩, rfl⟩

/-- `q_N` is at most the number of essential normalized descriptions. -/
theorem quotientDim_le_essential (r : ℕ) :
    quotientDim r ≤ (essentialKeys (normalizedKeys r)).card := by
  haveI : FiniteDimensional ℝ (auxSpan (r + 1 + 1)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  obtain ⟨S, hS⟩ : ∃ S : Submodule ℝ (Point (r + 1 + 1) → ℝ),
      S = Submodule.span ℝ (Set.range fun k : EssentialKey r => realUnitY k.1) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℝ S := hS ▸ FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hle := vocabularySpan_le_essential r
  rw [← hS] at hle
  have h1 := Submodule.finrank_le_finrank_of_le hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank S (auxSpan (r + 1 + 1))
  have h3 : FiniteDimensional.finrank ℝ S ≤ (essentialKeys (normalizedKeys r)).card := by
    rw [hS]
    exact (finrank_range_le_card (K := ℝ)).trans (Fintype.card_coe _).le
  rw [quotientDim_eq]
  exact Nat.sub_le_iff_le_add.mpr (h1.trans (h2.trans (Nat.add_le_add_right h3 _)))

/-- The quotient width never exceeds the width `secondWidth` of the main theorem. -/
theorem quotientDim_add_two_le_secondWidth (r : ℕ) (hr : 1 ≤ r) :
    quotientDim r + 2 ≤ secondWidth (r + 1 + 1) := by
  have h5 : (normalizedKeys r).card ≤ coneCount (r + 1 + 1) * 3 ^ r :=
    card_normalizedKeys_le_normalizedWordCones.trans
      (Nat.mul_le_mul_right _ (normalized_cone_count r))
  show quotientDim r + 2 ≤
    coneCount (r + 1 + 1) * 3 ^ (r + 1 + 1 - 2) - (r + 1 + 1) * (r + 1 + 1 - 1) + 2
  rw [show r + 1 + 1 - 2 = r by omega, show r + 1 + 1 - 1 = r + 1 by omega]
  exact Nat.add_le_add_right ((quotientDim_le_essential r).trans
    ((essentialNormalizedKeys_card_le_sub_orderedHinges hr).trans
      (Nat.sub_le_sub_right h5 _))) 2

end MaxCaterpillar
