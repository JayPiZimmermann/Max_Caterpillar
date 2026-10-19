import MaxNN.Constructions.Paramid.Caterpillar.Corrections.NormalizeFaces

/-! # Literal second-layer preactivation coefficients

All rows below are finite sums of coordinate and pair-feature coefficients.
No witness of membership in `PairLin` is selected to define a network row.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidChain MaxNN.Width

variable {n : ℕ}

noncomputable def pairMaxCoeff (a b : Fin n) : Fin (W n) → ℝ := by
  classical
  exact if h : a < b then coordCoef b + unitCoef (prIdx (prIdxOf a b h))
    else if h : b < a then coordCoef a + unitCoef (prIdx (prIdxOf b a h))
    else coordCoef a

theorem sum_pairMaxCoeff (a b : Fin n) (y : Fin (W n) → ℝ) :
    ∑ k, pairMaxCoeff a b k * y k = pairMaxLin a b y := by
  classical
  unfold pairMaxCoeff pairMaxLin
  split_ifs <;> simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib,
    sum_coordCoef, sum_unitCoef]

noncomputable def hingeCoeff (a b : Fin n) : Fin (W n) → ℝ :=
  pairMaxCoeff a b - coordCoef b

theorem sum_hingeCoeff (a b : Fin n) (x : Fin n → ℝ) :
    ∑ k, hingeCoeff a b k * feat n x k = relu (x a - x b) := by
  unfold hingeCoeff
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sum_pairMaxCoeff,
    sum_coordCoef, pairMaxLin_feat, coordLin_feat]
  rw [max_comm, max_eq_relu_add]
  ring

/-- Enumerating all endpoint pairs makes root decoding a finite formula. -/
noncomputable def rootHingeCoeff (v : Fin n → ℝ) : Fin (W (n + 1)) → ℝ := by
  classical
  exact ∑ p : Fin (n + 1) × Fin (n + 1),
    if p.1 ≠ p.2 ∧ v = toR (vtx p.1) - toR (vtx p.2)
    then hingeCoeff p.1 p.2 else 0

theorem rootHingeCoeff_difference (a b : Fin (n + 1)) (hab : a ≠ b) :
    rootHingeCoeff (toR (vtx a) - toR (vtx b)) = hingeCoeff a b := by
  classical
  unfold rootHingeCoeff
  rw [Finset.sum_eq_single (a, b)]
  · rw [if_pos ⟨hab, rfl⟩]
  · intro p _ hp
    rw [if_neg]
    rintro ⟨_, he⟩
    obtain ⟨ha, hb⟩ := simplex_difference_endpoints hab he
    exact hp (Prod.ext ha.symm hb.symm)
  · intro hp
    exact False.elim (hp (Finset.mem_univ _))

theorem rootHingeCoeff_zero : rootHingeCoeff (0 : Fin n → ℝ) = 0 := by
  classical
  unfold rootHingeCoeff
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  rintro ⟨hne, he⟩
  have he' : toR (vtx p.1) - toR (vtx p.2) = toR (vtx p.1) - toR (vtx p.1) := by
    rw [← he, sub_self]
  have h := simplex_difference_endpoints hne he'
  exact hne h.2.symm

theorem sum_rootHingeCoeff (v : Fin n → ℝ) (hv : IsSimplexDifference v)
    (x : Fin (n + 1) → ℝ) :
    ∑ k, rootHingeCoeff v k * feat (n + 1) x k =
      relu (dot v ((CoordAux.coordT n).mulVec x)) := by
  obtain ⟨a, b, rfl⟩ := hv
  by_cases hab : a = b
  · subst b
    simp only [sub_self, rootHingeCoeff_zero, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, CoordAux.dot_zero_left, relu_of_nonneg (le_refl (0 : ℝ))]
  · rw [rootHingeCoeff_difference a b hab, sum_hingeCoeff, SupportCut.dot_sub_left,
      MaxNN.Width.dot_toR_vtx_coordT, MaxNN.Width.dot_toR_vtx_coordT]
    congr 1
    ring

noncomputable def reducedLinearCoeff (γ : Fin n → ℝ) : Fin (W (n + 1)) → ℝ :=
  ∑ i : Fin n, γ i • (coordCoef i.succ - coordCoef (0 : Fin (n + 1)))

theorem sum_reducedLinearCoeff (γ : Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    ∑ k, reducedLinearCoeff γ k * feat (n + 1) x k =
      dot γ ((CoordAux.coordT n).mulVec x) := by
  unfold reducedLinearCoeff
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm, CoordAux.coordT_mulVec]
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    sum_coordCoef, coordLin_feat]

noncomputable def realUnitCoeff (k : RealKey n) : Fin (W (n + 1)) → ℝ :=
  reducedLinearCoeff k.1 + ∑ v in k.2, rootHingeCoeff v

theorem sum_realUnitCoeff (k : RealKey n)
    (hk : ∀ v ∈ k.2, IsSimplexDifference v) (x : Fin (n + 1) → ℝ) :
    ∑ j, realUnitCoeff k j * feat (n + 1) x j = realUnitArg k x := by
  unfold realUnitCoeff realUnitArg
  simp only [Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_add_distrib,
    sum_reducedLinearCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun v hv => sum_rootHingeCoeff v (hk v hv) x

end MaxNN.Caterpillar.Corrections
