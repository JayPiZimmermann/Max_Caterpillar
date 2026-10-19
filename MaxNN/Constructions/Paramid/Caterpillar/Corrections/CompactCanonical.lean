import MaxNN.Constructions.Paramid.Caterpillar.Corrections.CompactCovariance
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Table
import MaxNN.Core.Max

/-! # The canonical caterpillar network with the compact first layer -/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom MaxNN.Width

variable {n r : ℕ}

theorem coordT_mulVec_add_const (x : Fin (n + 1) → ℝ) (t : ℝ) :
    (CoordAux.coordT n).mulVec (fun i => x i + t) =
      (CoordAux.coordT n).mulVec x := by
  funext i
  rw [CoordAux.coordT_mulVec, CoordAux.coordT_mulVec]
  ring

theorem realUnitY_add_const (k : RealKey n) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    realUnitY k (fun i => x i + t) = realUnitY k x := by
  unfold realUnitY
  rw [coordT_mulVec_add_const]

noncomputable def compactDictionaryRows (K : Finset (RealKey n)) :
    Affine (compactWidth n) K.card where
  A := fun i => compactRealUnitCoeff (K.equivFin.symm i).1
  b := fun _ => 0

noncomputable def compactRemainderRows (q : Fin (compactWidth n) → ℝ) :
    Affine (compactWidth n) 2 where
  A := fun j => if j = 0 then q else -q
  b := fun _ => 0

noncomputable def compactDictionarySecondLayer (K : Finset (RealKey n))
    (q : Fin (compactWidth n) → ℝ) : Affine (compactWidth n) (K.card + 2) :=
  (compactDictionaryRows K).stack (compactRemainderRows q)

/-- The old output layer is dimension-compatible with the compact second
layer, so its literal coefficients are reused unchanged. -/
noncomputable def compactDictionaryNetwork (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (compactWidth n) → ℝ) : ReLUNet (n + 1) 1 2 :=
  ReLUNet.layer (compactFeatureLayer n)
    (ReLUNet.layer (compactDictionarySecondLayer K q)
      (ReLUNet.affine (dictionaryOutput K c)))

theorem compactDictionaryRows_eval (K : Finset (RealKey n))
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (x : Fin (n + 1) → ℝ) (i : Fin K.card) :
    (compactDictionaryRows K).eval (compactFeat n x) i =
      realUnitArg (K.equivFin.symm i).1 x := by
  change (∑ j, compactRealUnitCoeff (K.equivFin.symm i).1 j * compactFeat n x j) + 0 = _
  rw [add_zero, sum_compactRealUnitCoeff _ (hK _ (K.equivFin.symm i).2)]

theorem compactDictionaryNetwork_eval (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (compactWidth n) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (x : Fin (n + 1) → ℝ) :
    (compactDictionaryNetwork K c q).eval x 0 =
      ∑ k in K, c k * realUnitY k x + ∑ j, q j * compactFeat n x j := by
  unfold compactDictionaryNetwork
  rw [ReLUNet.eval_layer, ReLUNet.eval_layer, ReLUNet.eval_affine]
  change (∑ i : Fin (K.card + 2),
      (Fin.append (fun i => c (K.equivFin.symm i).1)
        (fun j : Fin 2 => if j = 0 then (1 : ℝ) else -1)) i *
      relu (((compactDictionaryRows K).stack (compactRemainderRows q)).eval
        (compactFeat n x) i)) + 0 = _
  rw [add_zero, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Affine.stack_eval_castAdd,
    Affine.stack_eval_natAdd, compactDictionaryRows_eval K hK]
  have hfirst : (∑ i : Fin K.card, c (K.equivFin.symm i).1 *
      relu (realUnitArg (K.equivFin.symm i).1 x)) =
      ∑ k in K, c k * realUnitY k x := by
    exact CoordAux.sum_equivFin_symm K (fun k => c k * realUnitY k x)
  rw [hfirst]
  congr 1
  rw [Fin.sum_univ_two]
  have hzero : (compactRemainderRows q).eval (compactFeat n x) 0 =
      ∑ j, q j * compactFeat n x j := by
    simp only [compactRemainderRows, Affine.eval, if_pos rfl, ite_true, add_zero]
  have hone : (compactRemainderRows q).eval (compactFeat n x) 1 =
      -(∑ j, q j * compactFeat n x j) := by
    simp only [compactRemainderRows, Affine.eval,
      if_neg (by decide : (1 : Fin 2) ≠ 0), Pi.neg_apply, neg_mul,
      Finset.sum_neg_distrib, add_zero]
  rw [hzero, hone]
  simp only [if_pos rfl, ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0),
    one_mul, neg_one_mul]
  exact (sub_eq_add_neg _ _).symm.trans (relu_sub_relu_neg _)

theorem compactDictionaryNetwork_computes (K : Finset (RealKey n))
    (c : RealKey n → ℝ) (q : Fin (compactWidth n) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ∀ x, f x = ∑ k in K, c k * realUnitY k x +
      ∑ j, q j * compactFeat n x j) :
    (compactDictionaryNetwork K c q).Computes f := by
  intro x
  rw [compactDictionaryNetwork_eval K c q hK x]
  exact (hf x).symm

namespace Canonical

noncomputable def canonicalRemainderFunction (r : ℕ) :
    (Fin (r + 1 + 1) → ℝ) → ℝ :=
  fun x => ∑ i, canonicalRemainderCoeff r i * feat (r + 1 + 1) x i

theorem canonicalRemainderFunction_pairLin :
    canonicalRemainderFunction r ∈ PairLin (r + 1 + 1) :=
  ⟨canonicalRemainderCoeff r, fun _ => rfl⟩

theorem canonicalRemainderFunction_diagonalEquivariant
    (hr : 1 ≤ r) (hclass : FormulaClassIdentity r) :
    DiagonalEquivariant (canonicalRemainderFunction r) := by
  intro x t
  let T := canonicalCorrectionTable r hr hclass
  have hshift := T.computes (fun i => x i + t)
  have hbase := T.computes x
  haveI : NeZero (r + 1 + 1) := ⟨by omega⟩
  rw [MaxNN.MAX_add_const] at hshift
  have hcorr :
      (∑ k in correctionKeys r, T.coeff k * realUnitY k (fun i => x i + t)) =
        ∑ k in correctionKeys r, T.coeff k * realUnitY k x := by
    apply Finset.sum_congr rfl
    intro k _
    rw [realUnitY_add_const]
  rw [hcorr] at hshift
  change MAX (r + 1 + 1) x + t =
    (∑ k in correctionKeys r, T.coeff k * realUnitY k x) +
      canonicalRemainderFunction r (fun i => x i + t) at hshift
  change MAX (r + 1 + 1) x =
    (∑ k in correctionKeys r, T.coeff k * realUnitY k x) +
      canonicalRemainderFunction r x at hbase
  linarith

/-- The literal compact coefficient vector of the canonical remainder. -/
noncomputable def compactCanonicalRemainderCoeff (r : ℕ) :
    Fin (compactWidth (r + 1)) → ℝ :=
  compactOfPairCoeff (canonicalRemainderCoeff r)

theorem sum_compactCanonicalRemainderCoeff (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) (x : Fin (r + 1 + 1) → ℝ) :
    ∑ j, compactCanonicalRemainderCoeff r j * compactFeat (r + 1) x j =
      canonicalRemainderFunction r x :=
  sum_compactOfPairCoeff_eq (fun _ => rfl)
    (canonicalRemainderFunction_diagonalEquivariant hr hclass) x

/-- Assumption-free compact network data. -/
noncomputable def compactCanonicalNetworkCandidate (r : ℕ) :
    ReLUNet (r + 1 + 1) 1 2 :=
  compactDictionaryNetwork (canonicalActiveKeys r) (canonicalNormalizedCoeff r)
    (compactCanonicalRemainderCoeff r)

theorem compactCanonicalNetworkCandidate_computes (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (compactCanonicalNetworkCandidate r).Computes (MAX (r + 1 + 1)) := by
  apply compactDictionaryNetwork_computes
  · intro k hk
    exact normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  · intro x
    have h := (canonicalCorrectionTable r hr hclass).computes_normalizedActive x
    rw [canonicalCorrectionTable_normalizedCoeff,
      canonicalCorrectionTable_normalizedActiveKeys] at h
    change MAX (r + 1 + 1) x =
      ∑ k in canonicalActiveKeys r, canonicalNormalizedCoeff r k * realUnitY k x +
        ∑ j, compactCanonicalRemainderCoeff r j * compactFeat (r + 1) x j
    rw [sum_compactCanonicalRemainderCoeff hr hclass]
    exact h

theorem compactCanonical_twoLayerWidth_normalizedActive (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (compactWidth (r + 1))
      ((canonicalActiveKeys r).card + 2) (MAX (r + 1 + 1)) := by
  refine ⟨compactFeatureLayer (r + 1),
    compactDictionarySecondLayer (canonicalActiveKeys r)
      (compactCanonicalRemainderCoeff r),
    ReLUNet.affine (dictionaryOutput (canonicalActiveKeys r)
      (canonicalNormalizedCoeff r)), ?_⟩
  exact compactCanonicalNetworkCandidate_computes hr hclass

end Canonical

end MaxNN.Caterpillar.Corrections
