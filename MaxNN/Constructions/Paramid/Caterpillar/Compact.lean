import MaxNN.Constructions.Paramid.Caterpillar.Bounds
import MaxNN.Constructions.Paramid.Caterpillar.Reduction
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.CompactTransport

/-! # Caterpillar networks with both width reductions combined -/

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

noncomputable def compactNetwork (r : ℕ) : ReLUNet (r + 1 + 1) 1 2 :=
  Canonical.compactCanonicalNetworkCandidate r

theorem compactNetwork_computes (r : ℕ) (hr : 1 ≤ r) :
    (compactNetwork r).Computes (MAX (r + 1 + 1)) :=
  Canonical.compactCanonicalNetworkCandidate_computes hr (formulaClassIdentity r hr)

theorem compact_twoLayerWidth (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1)
      ((r + 1 + 1).choose 2 + (r + 1 + 1) + 1)
      (secondWidth r) (MAX (r + 1 + 1)) := by
  rw [← compactWidth_eq]
  exact Canonical.compactCanonical_twoLayerWidth_normalizedActive hr
    (formulaClassIdentity r hr)

noncomputable def compactSparseNetwork (r : ℕ) : ReLUNet (r + 1 + 1) 1 2 :=
  compactOfDictionaryNetwork (Canonical.sparseKeys r)
    (Canonical.canonicalNormalizedCoeff r) (Canonical.canonicalRemainderCoeff r)

theorem compactSparseNetwork_computes (r : ℕ) (hr : 1 ≤ r) :
    (compactSparseNetwork r).Computes (MAX (r + 1 + 1)) :=
  compactOfDictionaryNetwork_computes_MAX _ _ _
    (Canonical.sparseKeys_simplexDifference r) (sparseNetwork_computes r hr)

theorem compactSparse_twoLayerWidth (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1)
      ((r + 1 + 1).choose 2 + (r + 1 + 1) + 1)
      (sparseSecondWidth r) (MAX (r + 1 + 1)) := by
  rw [← compactWidth_eq]
  refine ⟨compactFeatureLayer _, compactDictionarySecondLayer (Canonical.sparseKeys r)
      (compactOfPairCoeff (Canonical.canonicalRemainderCoeff r)),
    ReLUNet.affine (dictionaryOutput (Canonical.sparseKeys r)
      (Canonical.canonicalNormalizedCoeff r)), ?_⟩
  exact compactSparseNetwork_computes r hr

end MaxNN.Caterpillar

namespace MaxNN.Width

/-- Ordinary two-hidden-layer widths after compact feature recovery and
the path-reversal reduction, with equality on all real inputs. -/
theorem MAX_twoLayerWidth_caterpillar_compact (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    TwoLayerWidth N (N.choose 2 + N + 1)
      ((N.factorial * (2 ^ (N - 2) - 2) + N.factorial / 2) * 3 ^ (N - 2) + 2)
      (MAX N) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 + 1 := ⟨N - 2, by omega⟩
  rw [show r + 1 + 1 - 2 = r by omega]
  exact (Caterpillar.compact_twoLayerWidth r (by omega)).mono_right
    (Caterpillar.secondWidth_le_reversal r (by omega))

theorem MAX_twoLayerWidth_caterpillar_compact_sparse
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    TwoLayerWidth N (N.choose 2 + N + 1)
      (Caterpillar.sparseSecondWidth (N - 2)) (MAX N) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 + 1 := ⟨N - 2, by omega⟩
  rw [show r + 1 + 1 - 2 = r by omega]
  exact Caterpillar.compactSparse_twoLayerWidth r (by omega)

end MaxNN.Width
