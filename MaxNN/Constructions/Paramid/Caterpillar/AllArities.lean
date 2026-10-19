import MaxNN.Constructions.Paramid.Caterpillar.HingeBounds

/-! # The closed Fibonacci-hinge width bound in every positive arity -/

open BigOperators

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

noncomputable section

/-- A pair-linear `MAX (n+1)` can be compiled through the compact feature
layer with an empty correction dictionary and two signed output rows. -/
theorem compact_twoLayerWidth_of_MAX_pairLin (n : ℕ)
    (hMAX : MAX (n + 1) ∈ PairLin (n + 1)) :
    TwoLayerWidth (n + 1) ((n + 1).choose 2 + (n + 1) + 1) 2
      (MAX (n + 1)) := by
  obtain ⟨q, hq⟩ := hMAX
  have hold :
      (dictionaryNetwork (∅ : Finset (RealKey n)) (fun _ ↦ 0) q).Computes
        (MAX (n + 1)) := by
    apply dictionaryNetwork_computes
    · intro k hk
      exact False.elim (Finset.not_mem_empty k hk)
    · intro x
      simp only [Finset.sum_empty, zero_add]
      exact hq x
  have hcompact := compactOfDictionaryNetwork_computes_MAX
    (∅ : Finset (RealKey n)) (fun _ ↦ 0) q
    (by
      intro k hk
      exact False.elim (Finset.not_mem_empty k hk)) hold
  rw [← compactWidth_eq]
  refine ⟨compactFeatureLayer n,
    compactDictionarySecondLayer (∅ : Finset (RealKey n)) (compactOfPairCoeff q),
    ReLUNet.affine (dictionaryOutput (∅ : Finset (RealKey n)) (fun _ ↦ 0)), ?_⟩
  exact hcompact

theorem compact_twoLayerWidth_MAX_one :
    TwoLayerWidth 1 2 2 (MAX 1) := by
  apply compact_twoLayerWidth_of_MAX_pairLin 0
  rw [show MAX 1 = (fun x : Fin 1 → ℝ => x 0) from funext MAX_one]
  exact coord_mem_pairLin 0

theorem compact_twoLayerWidth_MAX_two :
    TwoLayerWidth 2 4 2 (MAX 2) := by
  apply compact_twoLayerWidth_of_MAX_pairLin 1
  rw [show MAX 2 = (fun x : Fin 2 → ℝ => max (x 0) (x 1)) from funext MAX_two]
  exact pairMax_mem_pairLin 0 1

end

end MaxNN.Caterpillar
