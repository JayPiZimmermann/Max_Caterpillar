import MaxCaterpillar.Fiber.GatingAbstractions.EmpiricalRegularity

set_option autoImplicit false
open MaxCaterpillar MaxCaterpillar.Fiber
open MaxCaterpillar.Fiber.GatingAbstractions
open MaxCaterpillar.Fiber.GatingAbstractions.Empirical

-- The parameter domain is the complete ordinary biased network space.
example : Params = ParameterSpace 4 6 3 := rfl
example : Network 4 6 3 ≃ₜ Params := networkHomeomorphParameters 4 6 3
example : FiniteDimensional.finrank ℝ Params = 55 := params_finrank

-- The empirical set compares actual outputs with Max4 on the stated fixed inputs.
example (p : Params) :
    p ∈ empiricalMaxSet ↔ ∀ i : Fin 4,
      (ofParams p).eval (samples i) = Maximum 4 (samples i) := Iff.rfl

-- The family itself is exact on every real input, not merely on those samples.
example (c : ℝ) (hc : 0 < c) (x : Point 4) :
    (ofParams (familyPoint c)).eval x = Maximum 4 x := by
  rw [ofParams_familyPoint]
  exact family_eval c hc.le x

-- No assumed Jacobian, assumed normal form, or unknown rank hypothesis.
example (c : ℝ) (hc : 0 < c) :
    HasStrictFDerivAt observations (observationsD (familyPoint c)) (familyPoint c) :=
  hasStrictFDerivAt_observations c hc
example (c : ℝ) (hc : 0 < c) : Function.Surjective (observationsD (familyPoint c)) :=
  observationsD_surjective c hc
example (c : ℝ) (hc : 0 < c) :
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint c))) empiricalMaxSet (familyPoint c) :=
  regular_empirical_max_fiber c hc
example (c : ℝ) (hc : 0 < c) :
    FiniteDimensional.finrank ℝ (LinearMap.ker (observationsD (familyPoint c))) = 51 :=
  empirical_kernel_finrank c hc

-- Both merger points are regular, even though their representations differ.
example :
    SameCompleteGates (family 1) (family 2) ∧
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
    ¬ Refines (family 2).secondHidden (family 1).secondHidden ∧
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint 1))) empiricalMaxSet (familyPoint 1) ∧
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint 2))) empiricalMaxSet (familyPoint 2) :=
  regular_same_gate_counterexample

#check @hasStrictFDerivAt_eval
#check @regular_empirical_max_fiber
#check @regular_same_gate_counterexample
#print axioms hasStrictFDerivAt_eval
#print axioms hasStrictFDerivAt_observations
#print axioms observationsD_surjective
#print axioms regular_empirical_max_fiber
#print axioms empirical_kernel_finrank
#print axioms regular_same_gate_counterexample
