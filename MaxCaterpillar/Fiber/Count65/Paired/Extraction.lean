import MaxCaterpillar.Fiber.Count65.Paired.PhysicalAtoms
import MaxCaterpillar.Fiber.Count65.Paired.EffectiveAtoms
import MaxCaterpillar.Fiber.Count65.Paired.Offsets

/-!
# Four-atom offset rigidity for an actual five-slot paired completion

This is an all-input theorem for ordinary networks. All real weights are
allowed. Ineffective gates remain physical network parameters and are removed
only from the proved finite atom index.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators
variable {m : ℕ}

/-- At every anchor pair, all nonzero normalized effective offsets coincide.
No recession activation pattern or cancellation ansatz is a hypothesis. -/
theorem network_effective_offsets_oneLevel (net : Network 4 6 m) (hm : m ≤ 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁ = pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (a b : ℝ) :
    OneLevel (fun k : EffectiveAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1) =>
      -(codeIntercept net.W₂ U a b k.val+net.W₂ k.val 0*(b-a))/net.W₂ k.val 0) := by
  let d := net.w₃
  let α := fun k => net.W₂ k 0
  let β := fun k => net.W₂ k 1
  have hh := network_two_increment_identity net U hU hb hnet a b
  apply oneLevel_of_atomBalance
    (fun k : EffectiveAtoms d α β => jumpWeights d α β k.val)
    (fun k : EffectiveAtoms d α β =>
      -(codeIntercept net.W₂ U a b k.val+α k.val*(b-a))/α k.val)
  · intro k
    exact k.property
  · exact effective_atomBalance_of_max a b d (codeIntercept net.W₂ U a b) α β hh
  · exact effectiveAtoms_card_le_four a b d (codeIntercept net.W₂ U a b) α β hm hh

end MaxCaterpillar.Fiber.Count65.Paired
