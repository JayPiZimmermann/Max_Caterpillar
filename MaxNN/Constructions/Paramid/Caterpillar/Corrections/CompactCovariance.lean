import MaxNN.Constructions.Paramid.Caterpillar.Corrections.CompactFeatures

/-! # Diagonal-equivariant pair-feature forms use the compact dictionary

The old pair-feature layer contains both signs of every coordinate.  A linear
readout which shifts by `t` under `x ↦ x + t·1` can discard all negative
coordinate features: after a sufficiently large diagonal shift they vanish,
the pair hinges stay fixed, and equivariance cancels the shift.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open MaxNN.Width

variable {N : ℕ}

def DiagonalEquivariant (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ x t, f (fun i => x i + t) = f x + t

theorem sum_pairFeature_blocks (a : Fin (W N) → ℝ) (x : Fin N → ℝ) :
    ∑ k, a k * feat N x k =
      (∑ i, a (posIdx i) * relu (x i)) +
      (∑ i, a (negIdx i) * relu (-(x i))) +
      ∑ q, a (prIdx q) * relu (x (prFst q) - x (prSnd q)) := by
  unfold W
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  change
    (∑ i, a (posIdx i) * feat N x (posIdx i)) +
      ((∑ i, a (negIdx i) * feat N x (negIdx i)) +
      ∑ q, a (prIdx q) * feat N x (prIdx q)) = _
  simp_rw [feat_pos, feat_neg, feat_pr]
  ring

noncomputable def positiveShift (x : Fin N → ℝ) : ℝ :=
  ∑ i, |x i|

theorem coordinate_add_positiveShift_nonneg (x : Fin N → ℝ) (i : Fin N) :
    0 ≤ x i + positiveShift x := by
  have hi : |x i| ≤ positiveShift x := by
    unfold positiveShift
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hneg : -x i ≤ |x i| := by
    rw [← abs_neg]
    exact le_abs_self (-x i)
  linarith

theorem sum_pairFeature_positiveShift (a : Fin (W N) → ℝ) (x : Fin N → ℝ) :
    ∑ k, a k * feat N (fun i => x i + positiveShift x) k =
      (∑ i, a (posIdx i) * (x i + positiveShift x)) +
      ∑ q, a (prIdx q) * relu (x (prFst q) - x (prSnd q)) := by
  rw [sum_pairFeature_blocks]
  simp_rw [relu_of_nonneg (coordinate_add_positiveShift_nonneg x _)]
  have hn : ∀ i : Fin N, relu (-(x i + positiveShift x)) = 0 := by
    intro i
    rw [relu_of_nonpos]
    linarith [coordinate_add_positiveShift_nonneg x i]
  simp_rw [hn]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  congr 2
  ring

theorem pairLin_zero {f : (Fin N → ℝ) → ℝ} {a : Fin (W N) → ℝ}
    (ha : ∀ x, f x = ∑ k, a k * feat N x k) :
    f 0 = 0 := by
  rw [ha]
  simp only [Pi.zero_apply, sum_pairFeature_blocks, relu_of_nonneg (le_refl (0 : ℝ)),
    neg_zero, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem sum_posCoeff_eq_one {f : (Fin N → ℝ) → ℝ} {a : Fin (W N) → ℝ}
    (ha : ∀ x, f x = ∑ k, a k * feat N x k)
    (heq : DiagonalEquivariant f) :
    ∑ i, a (posIdx i) = 1 := by
  have hshift := heq (0 : Fin N → ℝ) 1
  rw [ha, pairLin_zero ha] at hshift
  rw [sum_pairFeature_blocks] at hshift
  simp only [Pi.zero_apply, zero_add, relu_of_nonneg zero_le_one, mul_one,
    relu_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0), mul_zero, Finset.sum_const_zero,
    sub_self, add_zero, zero_add] at hshift
  have hz : relu (0 : ℝ) = 0 := relu_of_nonneg (le_refl 0)
  rw [hz] at hshift
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at hshift
  exact hshift

theorem equivariant_pairLin_formula {f : (Fin N → ℝ) → ℝ}
    {a : Fin (W N) → ℝ}
    (ha : ∀ x, f x = ∑ k, a k * feat N x k)
    (heq : DiagonalEquivariant f) (x : Fin N → ℝ) :
    f x = (∑ i, a (posIdx i) * x i) +
      ∑ q, a (prIdx q) * relu (x (prFst q) - x (prSnd q)) := by
  have hs := heq x (positiveShift x)
  rw [ha, sum_pairFeature_positiveShift] at hs
  have hmass := sum_posCoeff_eq_one ha heq
  have hdistrib :
      (∑ i, a (posIdx i) * (x i + positiveShift x)) =
        (∑ i, a (posIdx i) * x i) + positiveShift x := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have : (∑ i, a (posIdx i) * positiveShift x) = positiveShift x := by
      rw [← Finset.sum_mul, hmass, one_mul]
    rw [this]
  rw [hdistrib] at hs
  linarith

/-- Literal transport of an old pair-feature coefficient vector to the compact
dictionary.  Only positive-coordinate and unordered-pair entries survive. -/
noncomputable def compactOfPairCoeff (a : Fin (W (n + 1)) → ℝ) :
    Fin (compactWidth n) → ℝ :=
  (∑ i, a (posIdx i) • compactCoordCoeff i) +
    ∑ q, a (prIdx q) • compactHingeCoeff (prFst q) (prSnd q)

theorem sum_compactOfPairCoeff (a : Fin (W (n + 1)) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    ∑ k, compactOfPairCoeff a k * compactFeat n x k =
      (∑ i, a (posIdx i) * x i) +
      ∑ q, a (prIdx q) * relu (x (prFst q) - x (prSnd q)) := by
  unfold compactOfPairCoeff
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, sum_compactCoordCoeff, compactCoordLin_feat]
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, sum_compactHingeCoeff, compactHingeLin_feat]

theorem sum_compactOfPairCoeff_eq {f : (Fin (n + 1) → ℝ) → ℝ}
    {a : Fin (W (n + 1)) → ℝ}
    (ha : ∀ x, f x = ∑ k, a k * feat (n + 1) x k)
    (heq : DiagonalEquivariant f) (x : Fin (n + 1) → ℝ) :
    ∑ k, compactOfPairCoeff a k * compactFeat n x k = f x := by
  rw [sum_compactOfPairCoeff, equivariant_pairLin_formula ha heq]

theorem compactLin_of_pairLin_of_diagonalEquivariant
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : f ∈ PairLin (n + 1))
    (heq : DiagonalEquivariant f) : f ∈ CompactLin n := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨compactOfPairCoeff a, fun x => (sum_compactOfPairCoeff_eq ha heq x).symm⟩

end MaxNN.Caterpillar.Corrections
