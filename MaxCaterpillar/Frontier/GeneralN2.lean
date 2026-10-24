import MaxCaterpillar.Frontier.SecondWidthPlus
import MaxCaterpillar.Frontier.GeneralN

/-! # Joint width bound and free neurons (networks with biases)

* `second_width_half_succ`: one first-layer row with positive and one with negative coordinate
  sum force `h₂ ≥ ⌈N/2⌉ + 1`.
* `second_width_joint`: `6h₁ + 11N < 3N² + 18` forces `N + 2 ≤ 2h₂`.
* `free_neurons` (in `SecondWidthPlus`): `max_N = (one-hidden-layer) + K free neurons` needs
  `N ≤ 2K + 2`.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

/-- **Theorem H⁺.** If exactly one first-layer row has positive coordinate sum and exactly one has
negative coordinate sum, every network computing `max_N` has `N + 2 ≤ 2h₂`. -/
theorem second_width_half_succ [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x)
    (hp1 : (Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 1)
    (hq1 : (Finset.univ.filter fun j => ∑ i, net.W₁ j i < 0).card = 1) : N + 2 ≤ 2 * h₂ :=
  net.toZ.second_width_half_succ (net.toZ_eval_of_max h) hp1 hq1

/-- **Joint bound.** A network computing `max_N` whose first width is within two of the lower
bound of `first_width_quadratic` (`6h₁ + 11N < 3N² + 18`) has `N + 2 ≤ 2h₂`.
Conditional: it is not known whether any network satisfies the hypothesis (for `N = 3, 4`
none does: `Audit.second_width_joint_hyp_false_three`, `Audit.second_width_joint_hyp_false_four`). -/
theorem second_width_joint [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) (hh : 6 * h₁ + 11 * N < 3 * N * N + 18) :
    N + 2 ≤ 2 * h₂ :=
  net.toZ.second_width_joint (net.toZ_eval_of_max h) hh

end Frontier
end MaxCaterpillar
