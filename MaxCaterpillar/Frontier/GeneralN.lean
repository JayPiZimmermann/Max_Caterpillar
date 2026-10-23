import MaxCaterpillar.Frontier.FirstWidthN
import MaxCaterpillar.Frontier.SecondWidthN
import MaxCaterpillar.Frontier.Main
import MaxCaterpillar.Theorems

/-! # Width bounds for every `N` (networks with biases)

* `first_width_quadratic`: `3N² + 12 ≤ 6h₁ + 11N`, i.e. `h₁ ≥ C(N,2) - ⌊4N/3⌋ + 2`.
* `second_width_half`: `N ≤ 2h₂`, i.e. `h₂ ≥ ⌈N/2⌉`.
* `first_width_bounds`: the minimal first width lies between `C(N,2) - ⌊4N/3⌋ + 2` and
  `firstWidth N = C(N,2) + N + 1` (the latter attained by `caterpillar_net`).
Paper proofs: `research/sN/frontierN/PROOFS.md`.
-/

namespace MaxCaterpillar
namespace Frontier

variable {N h₁ h₂ : ℕ}

/-- **Theorem Q.** Every two-hidden-layer network computing `max_N` on `ℝ^N` has
`3N² + 12 ≤ 6h₁ + 11N`. -/
theorem first_width_quadratic [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : 3 * N * N + 12 ≤ 6 * h₁ + 11 * N :=
  net.toZ.first_width_quadratic (net.toZ_eval_of_max h)

/-- **Theorem H.** Every two-hidden-layer network computing `max_N` on `ℝ^N` has `N ≤ 2h₂`. -/
theorem second_width_half [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : N ≤ 2 * h₂ :=
  net.toZ.second_width_half (net.toZ_eval_of_max h)

/-- Combined second-width bound for `N ≥ 3`: `h₂ ≥ 3` and `2h₂ ≥ N`. -/
theorem second_width_bounds [NeZero N] (hN : 3 ≤ N) (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : 3 ≤ h₂ ∧ N ≤ 2 * h₂ :=
  ⟨second_width_ge_three hN net h, second_width_half net h⟩

/-- The first width needed for `max_N` is quadratic with leading term `N²/2`: some network of first
width `C(N,2) + N + 1` computes `max_N`, and every network has `3N² + 12 ≤ 6h₁ + 11N`. -/
theorem first_width_bounds (N : ℕ) [NeZero N] :
    (∃ net : Network N (firstWidth N) (secondWidth N), ∀ x, net.eval x = Maximum N x) ∧
    ∀ {h₁ h₂ : ℕ} (net : Network N h₁ h₂), (∀ x, net.eval x = Maximum N x) →
      3 * N * N + 12 ≤ 6 * h₁ + 11 * N := by
  obtain ⟨net, h, -, -⟩ := caterpillar_net N
  exact ⟨⟨net, h⟩, fun net h => first_width_quadratic net h⟩

end Frontier
end MaxCaterpillar
