import MaxNN.Constructions.Paramid.Caterpillar.Corrections.CompactCanonical

/-! # Compress the first layer of any dictionary representation of MAX -/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open MaxNN.Width

variable {n : ℕ}

/-- Keep every dictionary coefficient and second-layer key, and replace
the pair-feature remainder by its compact coefficient vector. -/
noncomputable def compactOfDictionaryNetwork (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (W (n + 1)) → ℝ) : ReLUNet (n + 1) 1 2 :=
  compactDictionaryNetwork K c (compactOfPairCoeff q)

theorem compactOfDictionaryNetwork_computes_MAX (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (W (n + 1)) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (hnet : (dictionaryNetwork K c q).Computes (MAX (n + 1))) :
    (compactOfDictionaryNetwork K c q).Computes (MAX (n + 1)) := by
  let f : (Fin (n + 1) → ℝ) → ℝ := fun x => ∑ j, q j * feat (n + 1) x j
  have hf (x : Fin (n + 1) → ℝ) :
      MAX (n + 1) x = ∑ k in K, c k * realUnitY k x + f x :=
    (hnet x).symm.trans (dictionaryNetwork_eval K c q hK x)
  have heq : DiagonalEquivariant f := by
    intro x t
    have hs := hf (fun i => x i + t)
    have hb := hf x
    rw [MaxNN.MAX_add_const] at hs
    have hsum : (∑ k in K, c k * realUnitY k (fun i => x i + t)) =
        ∑ k in K, c k * realUnitY k x :=
      Finset.sum_congr rfl fun k _ => by rw [realUnitY_add_const]
    rw [hsum] at hs
    linarith
  apply compactDictionaryNetwork_computes K c (compactOfPairCoeff q) hK
  intro x
  rw [sum_compactOfPairCoeff_eq (f := f) (fun _ => rfl) heq x]
  exact hf x

end MaxNN.Caterpillar.Corrections
