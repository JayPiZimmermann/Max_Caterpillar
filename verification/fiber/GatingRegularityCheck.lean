import MaxCaterpillar.Fiber.GatingAbstractions.Regularity
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityTopology
import MaxCaterpillar.Fiber.GatingAbstractions.RegularitySplit
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityChart

set_option autoImplicit false
noncomputable section

open MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.GatingAbstractions

/-- Check the actual meaning of regularity: an ambient coordinate chart,
with invertible strict derivative, straightening the whole stated set. -/
example (S : Set Raw) (a : Raw) :
    HasRegularFiberChartAt (V := Fin 28 → ℝ) (W := Free) S a ↔
      ∃ (e : PartialHomeomorph Raw ((Fin 28 → ℝ) × Free))
        (L : Raw ≃L[ℝ] ((Fin 28 → ℝ) × Free)),
        a ∈ e.source ∧
        HasStrictFDerivAt (e : Raw → (Fin 28 → ℝ) × Free)
          (L : Raw →L[ℝ] (Fin 28 → ℝ) × Free) a ∧
        ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = (e a).1 := Iff.rfl

example : Raw ≃ₜ {net : Network 4 6 3 // net.HasZeroBiases} :=
  rawHomeomorphZeroBias

example : ↥RawExactSet ≃ₜ {net : ExactFiber 4 6 3 // net.val.HasZeroBiases} :=
  rawHomeomorphZeroBiasExact

example (net : Network 4 6 3) (hz : net.HasZeroBiases) :
    fromRaw (toRaw net) = net := fromRaw_toRaw net hz

example (p : Raw) : toRaw (fromRaw p) = p := toRaw_fromRaw p

example : Raw ≃L[ℝ] ((Fin 28 → ℝ) × Free) := splitCoordinates

/-- Check both the forward and inverse smoothness, the invertible derivative,
and the local equality with the entire stated exact fiber. -/
example (S : Set Raw) (a : Raw) :
    HasSmoothRegularFiberChartAt (V := Fin 28 → ℝ) (W := Free) S a ↔
      ∃ (e : PartialHomeomorph Raw ((Fin 28 → ℝ) × Free))
        (L : Raw ≃L[ℝ] ((Fin 28 → ℝ) × Free)),
        a ∈ e.source ∧
        HasStrictFDerivAt (e : Raw → (Fin 28 → ℝ) × Free)
          (L : Raw →L[ℝ] (Fin 28 → ℝ) × Free) a ∧
        ContDiffAt ℝ ⊤ (e : Raw → (Fin 28 → ℝ) × Free) a ∧
        ContDiffAt ℝ ⊤ (e.symm : (Fin 28 → ℝ) × Free → Raw) (e a) ∧
        ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = (e a).1 := Iff.rfl

/-- The endpoint statements have no rank, classification or genericity
assumptions left over. -/
example : HasSmoothRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ)
    {p : Fin 45 → ℝ | ∀ x : Point 4, (fromRaw p).eval x = Maximum 4 x}
    (toRaw (family 1)) := smooth_regular_family_one

example : HasSmoothRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ)
    {p : Fin 45 → ℝ | ∀ x : Point 4, (fromRaw p).eval x = Maximum 4 x}
    (toRaw (family 2)) := smooth_regular_family_two

example : HasRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ)
    RawExactSet (toRaw (family 1)) := regular_family_one

example : HasRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ)
    RawExactSet (toRaw (family 2)) := regular_family_two

#check @eventual_fiber_iff_of_inverse_coordinates
#check @regular_fiber_chart_of_inverse_coordinates
#check @regular_level_set_chart
#check @rawHomeomorphZeroBiasExact
#print axioms eventual_fiber_iff_of_inverse_coordinates
#print axioms regular_fiber_chart_of_inverse_coordinates
#print axioms regular_level_set_chart
#print axioms rawHomeomorphZeroBias
#print axioms rawHomeomorphZeroBiasExact
#print axioms splitCoordinates
#print axioms smooth_regular_family_one
#print axioms smooth_regular_family_two
#print axioms regular_family_one
#print axioms regular_family_two
