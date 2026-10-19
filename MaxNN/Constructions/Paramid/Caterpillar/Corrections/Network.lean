import MaxNN.Constructions.Paramid.Caterpillar.Corrections.NetworkCoefficients

/-! # The literal two-hidden-layer caterpillar network

The first layer is the shared pair-feature layer. The second layer has one row
per finite dictionary key, followed by the positive and negative remainder
rows. The output sums the supplied dictionary coefficients and subtracts the
last remainder neuron from the preceding one.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom MaxNN.Width

variable {n r : ℕ}

noncomputable def dictionaryRows (K : Finset (RealKey n)) : Affine (W (n + 1)) K.card where
  A := fun i => realUnitCoeff (K.equivFin.symm i).1
  b := fun _ => 0

noncomputable def remainderRows (q : Fin (W (n + 1)) → ℝ) : Affine (W (n + 1)) 2 where
  A := fun j => if j = 0 then q else -q
  b := fun _ => 0

noncomputable def dictionarySecondLayer (K : Finset (RealKey n))
    (q : Fin (W (n + 1)) → ℝ) : Affine (W (n + 1)) (K.card + 2) :=
  (dictionaryRows K).stack (remainderRows q)

noncomputable def dictionaryOutput (K : Finset (RealKey n)) (c : RealKey n → ℝ) :
    Affine (K.card + 2) 1 where
  A := fun _ => Fin.append (fun i => c (K.equivFin.symm i).1)
    (fun j : Fin 2 => if j = 0 then 1 else -1)
  b := fun _ => 0

/-- A closed two-layer network definition, with no smaller-arity calls. -/
noncomputable def dictionaryNetwork (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ) : ReLUNet (n + 1) 1 2 :=
  ReLUNet.layer (featureLayer (n + 1))
    (ReLUNet.layer (dictionarySecondLayer K q) (ReLUNet.affine (dictionaryOutput K c)))

theorem dictionaryRows_eval (K : Finset (RealKey n))
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (x : Fin (n + 1) → ℝ) (i : Fin K.card) :
    (dictionaryRows K).eval (feat (n + 1) x) i =
      realUnitArg (K.equivFin.symm i).1 x := by
  change (∑ j, realUnitCoeff (K.equivFin.symm i).1 j * feat (n + 1) x j) + 0 = _
  rw [add_zero, sum_realUnitCoeff _ (hK _ (K.equivFin.symm i).2)]

theorem dictionaryNetwork_eval (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v) (x : Fin (n + 1) → ℝ) :
    (dictionaryNetwork K c q).eval x 0 =
      ∑ k in K, c k * realUnitY k x + ∑ j, q j * feat (n + 1) x j := by
  unfold dictionaryNetwork
  rw [ReLUNet.eval_layer, ReLUNet.eval_layer, ReLUNet.eval_affine]
  change (∑ i : Fin (K.card + 2),
      (Fin.append (fun i => c (K.equivFin.symm i).1)
        (fun j : Fin 2 => if j = 0 then (1 : ℝ) else -1)) i *
      relu (((dictionaryRows K).stack (remainderRows q)).eval (feat (n + 1) x) i)) + 0 = _
  rw [add_zero, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Affine.stack_eval_castAdd,
    Affine.stack_eval_natAdd, dictionaryRows_eval K hK]
  have hfirst : (∑ i : Fin K.card, c (K.equivFin.symm i).1 *
      relu (realUnitArg (K.equivFin.symm i).1 x)) = ∑ k in K, c k * realUnitY k x := by
    exact CoordAux.sum_equivFin_symm K (fun k => c k * realUnitY k x)
  rw [hfirst]
  congr 1
  rw [Fin.sum_univ_two]
  have hzero : (remainderRows q).eval (feat (n + 1) x) 0 =
      ∑ j, q j * feat (n + 1) x j := by
    simp only [remainderRows, Affine.eval, if_pos rfl, ite_true, add_zero]
  have hone : (remainderRows q).eval (feat (n + 1) x) 1 =
      -(∑ j, q j * feat (n + 1) x j) := by
    simp only [remainderRows, Affine.eval, if_neg (by decide : (1 : Fin 2) ≠ 0),
      Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, add_zero]
  rw [hzero, hone]
  simp only [if_pos rfl, ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0), one_mul, neg_one_mul]
  exact (sub_eq_add_neg _ _).symm.trans (relu_sub_relu_neg _)

/-- Use any supplied literal feature coefficients for the remainder. The
remaining rows and output coefficients are defined above, not extracted from
an existential network theorem. -/
theorem dictionaryNetwork_computes (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ)
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ∀ x, f x = ∑ k in K, c k * realUnitY k x + ∑ j, q j * feat (n + 1) x j) :
    (dictionaryNetwork K c q).Computes f := by
  intro x
  rw [dictionaryNetwork_eval K c q hK x]
  exact (hf x).symm

noncomputable def CorrectionTable.normalizedNetwork (T : CorrectionTable r)
    (q : Fin (W (r + 1 + 1)) → ℝ) : ReLUNet (r + 1 + 1) 1 2 :=
  dictionaryNetwork T.normalizedActiveKeys T.normalizedCoeff q

theorem CorrectionTable.normalizedNetwork_computes (T : CorrectionTable r)
    (q : Fin (W (r + 1 + 1)) → ℝ)
    (hq : ∀ x, T.remainder x = ∑ j, q j * feat (r + 1 + 1) x j) :
    (T.normalizedNetwork q).Computes (MAX (r + 1 + 1)) := by
  apply dictionaryNetwork_computes
  · intro k hk
    exact normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  · intro x
    rw [T.computes_normalizedActive x, hq x]

end MaxNN.Caterpillar.Corrections
