import MaxNN.Constructions.Paramid.Caterpillar.Construction
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Sparse

/-! # The support-minimized caterpillar network

This construction minimizes support with the canonical coefficients and
pair-feature remainder held fixed. Correctness holds for every arity at
least three; no formula-class hypothesis is required.
-/

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

noncomputable def sparseSecondWidth (r : ℕ) : ℕ :=
  (Canonical.sparseKeys r).card + 2

noncomputable def sparseNetwork (r : ℕ) : ReLUNet (r + 1 + 1) 1 2 :=
  Canonical.sparseNetworkCandidate r

theorem sparseNetwork_computes (r : ℕ) (hr : 1 ≤ r) :
    (sparseNetwork r).Computes (MAX (r + 1 + 1)) :=
  Canonical.sparseNetworkCandidate_computes r hr (formulaClassIdentity r hr)

theorem sparseSecondWidth_le (r : ℕ) : sparseSecondWidth r ≤ secondWidth r :=
  Nat.add_le_add_right (Canonical.sparseKeys_card_le r) 2

theorem sparse_twoLayerWidth (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1) (firstWidth r) (sparseSecondWidth r)
      (MAX (r + 1 + 1)) := by
  refine ⟨featureLayer _, dictionarySecondLayer (Canonical.sparseKeys r)
      (Canonical.canonicalRemainderCoeff r),
    ReLUNet.affine (dictionaryOutput (Canonical.sparseKeys r)
      (Canonical.canonicalNormalizedCoeff r)), ?_⟩
  exact sparseNetwork_computes r hr

theorem sparseSecondWidth_le_factorial (r : ℕ) :
    sparseSecondWidth r ≤ (r + 1 + 1).factorial * (2 ^ r - 1) * 3 ^ r + 2 :=
  (sparseSecondWidth_le r).trans (secondWidth_le_factorial r)

end MaxNN.Caterpillar

namespace MaxNN.Width

theorem MAX_twoLayerWidth_caterpillar_sparse (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    TwoLayerWidth N (N.choose 2 + 2 * N)
      (Caterpillar.sparseSecondWidth (N - 2)) (MAX N) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 + 1 := ⟨N - 2, by omega⟩
  rw [show r + 1 + 1 - 2 = r by omega, ← Caterpillar.firstWidth_eq]
  exact Caterpillar.sparse_twoLayerWidth r (by omega)

end MaxNN.Width
