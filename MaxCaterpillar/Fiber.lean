import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Components
import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Fiber.Feasibility
import MaxCaterpillar.Fiber.BiasQuotient
import MaxCaterpillar.Fiber.Disconnected65
import MaxCaterpillar.Fiber.NaturalInterventions
import MaxCaterpillar.Fiber.GatingAbstractions
import MaxCaterpillar.Fiber.GatingAbstractions.EmpiricalRegularity
import MaxCaterpillar.Fiber.GatingAbstractions.RegularCounterexample
import MaxCaterpillar.Fiber.BinaryPatterns
import MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexitySigns
import MaxCaterpillar.Fiber.Count65

/-! # Exact ReLU parameter fibers

This interface uses the ordinary topology on all network parameters, equality
on every real input, and the quotient by positive neuron rescaling and hidden
and input permutations. It includes the Max4 feasibility frontier and the
component-preserving reduction from arbitrary biases to zero biases.

The full Max4 `(6,5)` fiber has exactly 65 connected components after all the
stated symmetries; see `max4_6_5_has_65_components`. Arbitrary biases are included.

The interface also includes explicit path-connected counterexamples showing
that natural hidden activations do not determine neuron-interchange behavior,
and that binary activation patterns can change within an exact fiber component.
Conversely, equal labelled binary maps at both layers and matching nonzero
output signs suffice for an exact parameter path, without fixing the first layer.
The gating counterexample has incomparable input representation partitions
inside a fixed gating cell. Its regularity statements distinguish the full
biased empirical fiber from the full all-input zero-bias exact fiber.

`HasComponentCount` states an exact count for this genuine quotient. The
`(6,5)` proof classifies actual first matrices and physical completions into
one paired component, 32 mixed components, and 32 star components. Proposed
counts at widths `(6,3)` and `(6,4)` are separate statements, not asserted here.
-/
