import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Components
import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Fiber.Feasibility
import MaxCaterpillar.Fiber.BiasQuotient
import MaxCaterpillar.Fiber.Disconnected65

/-! # Exact ReLU parameter fibers

This interface uses the ordinary topology on all network parameters, equality
on every real input, and the quotient by positive neuron rescaling and hidden
and input permutations. It includes the Max4 feasibility frontier and the
component-preserving reduction from arbitrary biases to zero biases.

The full Max4 `(6,5)` fiber has at least two connected components, even after
all the stated symmetries; see `max4_6_5_at_least_two_components`.

`HasComponentCount` states an exact count for this genuine quotient. The
proposed Max4 counts at widths `(6,3)`, `(6,4)`, and `(6,5)` have not yet been
proved here: the exhaustive network classification remains to be formalized.
-/
