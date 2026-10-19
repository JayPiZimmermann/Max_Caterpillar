import MaxNN.Constructions.Paramid.Caterpillar.Compact
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.AbsorbHinges

/-! # Remove correction rows already supplied by the first layer

This is a direct coefficient transformation, without support search or
coefficient reoptimization. The earlier networks remain separately defined.
-/

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

noncomputable def essentialSecondWidth (r : ℕ) : ℕ :=
  (essentialKeys (Canonical.canonicalActiveKeys r)).card + 2

noncomputable def essentialNetwork (r : ℕ) : ReLUNet (r + 1 + 1) 1 2 :=
  absorbedNetwork (Canonical.canonicalActiveKeys r) (Canonical.canonicalNormalizedCoeff r)
    (Canonical.canonicalRemainderCoeff r)

theorem essentialNetwork_computes (r : ℕ) (hr : 1 ≤ r) :
    (essentialNetwork r).Computes (MAX (r + 1 + 1)) := by
  apply absorbedNetwork_computes_of_dictionaryNetwork_computes
  · intro k hk
    exact normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  · exact network_computes r hr

theorem essentialSecondWidth_le (r : ℕ) : essentialSecondWidth r ≤ secondWidth r :=
  absorbed_secondWidth_le _

/-- The exact saving equals the number of absorbable nonzero hinge rows. -/
theorem essentialSecondWidth_add_removed (r : ℕ) :
    essentialSecondWidth r + (hingeKeys (Canonical.canonicalActiveKeys r)).card =
      secondWidth r := by
  unfold essentialSecondWidth secondWidth
  rw [Nat.add_right_comm, essentialKeys_card_add_hingeKeys_card]

noncomputable def compactEssentialNetwork (r : ℕ) : ReLUNet (r + 1 + 1) 1 2 :=
  compactOfDictionaryNetwork (essentialKeys (Canonical.canonicalActiveKeys r))
    (Canonical.canonicalNormalizedCoeff r)
    (absorbedRemainderCoeff (Canonical.canonicalActiveKeys r)
      (Canonical.canonicalNormalizedCoeff r) (Canonical.canonicalRemainderCoeff r))

theorem compactEssentialNetwork_computes (r : ℕ) (hr : 1 ≤ r) :
    (compactEssentialNetwork r).Computes (MAX (r + 1 + 1)) := by
  apply compactOfDictionaryNetwork_computes_MAX
  · apply essentialKeys_labels
    intro k hk
    exact normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  · exact essentialNetwork_computes r hr

theorem essential_twoLayerWidth (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1) (firstWidth r) (essentialSecondWidth r)
      (MAX (r + 1 + 1)) := by
  apply absorbedNetwork_twoLayerWidth
  · intro k hk
    exact normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  · exact network_computes r hr

theorem compactEssential_twoLayerWidth (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1)
      ((r + 1 + 1).choose 2 + (r + 1 + 1) + 1)
      (essentialSecondWidth r) (MAX (r + 1 + 1)) := by
  rw [← compactWidth_eq]
  refine ⟨compactFeatureLayer _, compactDictionarySecondLayer
      (essentialKeys (Canonical.canonicalActiveKeys r))
      (compactOfPairCoeff (absorbedRemainderCoeff (Canonical.canonicalActiveKeys r)
        (Canonical.canonicalNormalizedCoeff r) (Canonical.canonicalRemainderCoeff r))),
    ReLUNet.affine (dictionaryOutput (essentialKeys (Canonical.canonicalActiveKeys r))
      (Canonical.canonicalNormalizedCoeff r)), ?_⟩
  exact compactEssentialNetwork_computes r hr

end MaxNN.Caterpillar

namespace MaxNN.Width

theorem MAX_twoLayerWidth_caterpillar_essential (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    TwoLayerWidth N (N.choose 2 + N + 1)
      (Caterpillar.essentialSecondWidth (N - 2)) (MAX N) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 + 1 := ⟨N - 2, by omega⟩
  rw [show r + 1 + 1 - 2 = r by omega]
  exact Caterpillar.compactEssential_twoLayerWidth r (by omega)

end MaxNN.Width
