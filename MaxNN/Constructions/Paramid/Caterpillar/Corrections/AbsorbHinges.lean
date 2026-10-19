import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Network

/-!
# Absorbing hinge correction rows into the first-layer remainder

A dictionary key with no inner labels and simplex-difference outer normal is
already a pair hinge produced by the shared first layer.  This file removes
all such keys from the second layer and adds their exact coefficients to the
linear feature remainder.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom MaxNN.Width

variable {n : ℕ}

noncomputable local instance absorbHingesPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
noncomputable local instance absorbHingesRealKeyDecidableEq (m : ℕ) : DecidableEq (RealKey m) :=
  Classical.decEq _

/-- Correction keys whose whole unit is already a first-layer pair hinge. -/
noncomputable def hingeKeys (K : Finset (RealKey n)) : Finset (RealKey n) := by
  classical
  exact K.filter fun k ↦ k.2 = ∅ ∧ IsSimplexDifference k.1

/-- The genuinely second-layer part of a correction dictionary. -/
noncomputable def essentialKeys (K : Finset (RealKey n)) : Finset (RealKey n) :=
  K \ hingeKeys K

/-- Add the removed hinge coefficients to the existing feature remainder. -/
noncomputable def absorbedRemainderCoeff (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (W (n + 1)) → ℝ) :
    Fin (W (n + 1)) → ℝ :=
  q + ∑ k in hingeKeys K, c k • rootHingeCoeff k.1

/-- The literal smaller network obtained by deleting all absorbable hinge
rows and changing only the feature-remainder coefficients. -/
noncomputable def absorbedNetwork (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (W (n + 1)) → ℝ) :
    ReLUNet (n + 1) 1 2 :=
  dictionaryNetwork (essentialKeys K) c (absorbedRemainderCoeff K c q)

theorem hingeKeys_subset (K : Finset (RealKey n)) : hingeKeys K ⊆ K := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

theorem essentialKeys_subset (K : Finset (RealKey n)) : essentialKeys K ⊆ K := by
  unfold essentialKeys
  intro k hk
  exact (Finset.mem_sdiff.mp hk).1

theorem hingeKey_empty {K : Finset (RealKey n)} {k : RealKey n}
    (hk : k ∈ hingeKeys K) : k.2 = ∅ :=
  (Finset.mem_filter.mp hk).2.1

theorem hingeKey_simplexDifference {K : Finset (RealKey n)} {k : RealKey n}
    (hk : k ∈ hingeKeys K) : IsSimplexDifference k.1 :=
  (Finset.mem_filter.mp hk).2.2

theorem realUnitY_hingeKey (K : Finset (RealKey n)) {k : RealKey n}
    (hk : k ∈ hingeKeys K) (x : Fin (n + 1) → ℝ) :
    realUnitY k x = ∑ j, rootHingeCoeff k.1 j * feat (n + 1) x j := by
  rw [sum_rootHingeCoeff k.1 (hingeKey_simplexDifference hk) x]
  rw [realUnitY_eq_relu, realUnitArg, hingeKey_empty hk,
    Finset.sum_empty, add_zero]

theorem sum_absorbedRemainderCoeff (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (W (n + 1)) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    ∑ j, absorbedRemainderCoeff K c q j * feat (n + 1) x j =
      (∑ k in hingeKeys K, c k * realUnitY k x) +
        ∑ j, q j * feat (n + 1) x j := by
  unfold absorbedRemainderCoeff
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  calc
    ∑ j, c k * rootHingeCoeff k.1 j * feat (n + 1) x j =
        ∑ j, c k * (rootHingeCoeff k.1 j * feat (n + 1) x j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc]
    _ = c k * ∑ j, rootHingeCoeff k.1 j * feat (n + 1) x j := by
      rw [Finset.mul_sum]
    _ = c k * realUnitY k x := by rw [realUnitY_hingeKey K hk x]

theorem sum_essential_add_absorbedRemainder
    (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ) (x : Fin (n + 1) → ℝ) :
    (∑ k in essentialKeys K, c k * realUnitY k x) +
        ∑ j, absorbedRemainderCoeff K c q j * feat (n + 1) x j =
      (∑ k in K, c k * realUnitY k x) +
        ∑ j, q j * feat (n + 1) x j := by
  rw [sum_absorbedRemainderCoeff]
  rw [← add_assoc]
  change ((∑ k in K \ hingeKeys K, c k * realUnitY k x) +
      ∑ k in hingeKeys K, c k * realUnitY k x) +
        ∑ j, q j * feat (n + 1) x j = _
  rw [Finset.sum_sdiff (hingeKeys_subset K)]

theorem essentialKeys_labels
    (K : Finset (RealKey n))
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v) :
    ∀ k ∈ essentialKeys K, ∀ v ∈ k.2, IsSimplexDifference v := by
  intro k hk v hv
  exact hK k (essentialKeys_subset K hk) v hv

/-- The transformed literal network has exactly the same output function. -/
theorem absorbedNetwork_eval (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (W (n + 1)) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (x : Fin (n + 1) → ℝ) :
    (absorbedNetwork K c q).eval x 0 = (dictionaryNetwork K c q).eval x 0 := by
  rw [absorbedNetwork, dictionaryNetwork_eval _ _ _
      (essentialKeys_labels K hK) x,
    dictionaryNetwork_eval K c q hK x]
  exact sum_essential_add_absorbedRemainder K c q x

/-- Correctness transfers directly from the old literal dictionary network. -/
theorem absorbedNetwork_computes_of_dictionaryNetwork_computes
    (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    {f : (Fin (n + 1) → ℝ) → ℝ}
    (hold : (dictionaryNetwork K c q).Computes f) :
    (absorbedNetwork K c q).Computes f := by
  intro x
  rw [absorbedNetwork_eval K c q hK x]
  exact hold x

theorem essentialKeys_card_le (K : Finset (RealKey n)) :
    (essentialKeys K).card ≤ K.card :=
  Finset.card_le_of_subset (essentialKeys_subset K)

theorem essentialKeys_card_add_hingeKeys_card (K : Finset (RealKey n)) :
    (essentialKeys K).card + (hingeKeys K).card = K.card := by
  unfold essentialKeys
  exact Finset.card_sdiff_add_card_eq_card (hingeKeys_subset K)

theorem absorbed_secondWidth_le (K : Finset (RealKey n)) :
    (essentialKeys K).card + 2 ≤ K.card + 2 :=
  Nat.add_le_add_right (essentialKeys_card_le K) 2

/-- The transformed network witnesses its literal second width. -/
theorem absorbedNetwork_twoLayerWidth
    (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    {f : (Fin (n + 1) → ℝ) → ℝ}
    (hold : (dictionaryNetwork K c q).Computes f) :
    TwoLayerWidth (n + 1) (W (n + 1)) ((essentialKeys K).card + 2) f := by
  refine ⟨featureLayer (n + 1),
    dictionarySecondLayer (essentialKeys K) (absorbedRemainderCoeff K c q),
    ReLUNet.affine (dictionaryOutput (essentialKeys K) c), ?_⟩
  exact absorbedNetwork_computes_of_dictionaryNetwork_computes K c q hK hold

end MaxNN.Caterpillar.Corrections
