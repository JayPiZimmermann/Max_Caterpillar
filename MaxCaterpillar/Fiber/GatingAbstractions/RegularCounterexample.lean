import MaxCaterpillar.Fiber.GatingAbstractions
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityChart

/-!
# A regular exact-fiber counterexample to gating-determined representation order

The networks agree with Max4 on every real input, have identical complete
gating maps, and lie on one exact parameter path. Their representation
partitions are incomparable. At both endpoints the entire zero-bias exact
fiber, allowing all forty-five weights to vary, has a smooth ambient chart.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.GatingAbstractions

theorem regular_same_gate_exact_counterexample :
    (∀ x, (family 1).eval x = Maximum 4 x) ∧
    (∀ x, (family 2).eval x = Maximum 4 x) ∧
    SameCompleteGates (family 1) (family 2) ∧
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
    ¬ Refines (family 2).secondHidden (family 1).secondHidden ∧
    Joined oneExact twoExact ∧
    HasSmoothRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family 1)) ∧
    HasSmoothRegularFiberChartAt (V := Observed) (W := Free)
      RawExactSet (toRaw (family 2)) := by
  obtain ⟨h₁, h₂, hg, hr₁, hr₂⟩ := same_gates_different_representations
  exact ⟨h₁, h₂, hg, hr₁, hr₂, exact_points_joined,
    smooth_regular_family_one, smooth_regular_family_two⟩

#print axioms regular_same_gate_exact_counterexample

end MaxCaterpillar.Fiber.GatingAbstractions
