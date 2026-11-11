import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Localize

/-! Literal function-level consumer of the core-removal theorem. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores.Check
open BigOperators Frontier

example {N m : ℕ} [NeZero N] [NeZero m] {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (R : Point N → ℝ) (g : κ → Point N → ℝ) (d : κ → ℝ)
    (hR : IsShallow R) (hg : ∀ j, IsShallow (g j))
    (hc : ∀ j, ConvexOn ℝ Set.univ (g j))
    (heq : ∀ x, R x + ∑ j, d j * relu (g j x) = Maximum N x)
    (e : Fin m ↪ Fin N) (q : Point N) (M : ℝ)
    (hq : ∀ a, q (e a) = M)
    (hbelow : ∀ i, i ∉ Finset.univ.image e → q i < M)
    (k : κ) (hk : g k q ≠ 0) :
    ∃ (R' : Point m → ℝ) (g' : {j : κ // j ≠ k} → Point m → ℝ)
      (d' : {j : κ // j ≠ k} → ℝ),
      IsShallow R' ∧ (∀ j, IsShallow (g' j)) ∧
        (∀ j, ConvexOn ℝ Set.univ (g' j)) ∧
        (∀ x, R' x + ∑ j, d' j * relu (g' j x) = Maximum m x) := by
  let net : ConvexRepresentation N κ := ⟨R, g, d, hR, hg, hc, heq⟩
  obtain ⟨net'⟩ := net.localize e q M hq hbelow k hk
  exact ⟨net'.remainder, net'.core, net'.weight, net'.shallow_remainder,
    net'.shallow_core, net'.convex_core, net'.computes⟩

#print axioms ConvexRepresentation.localize
end MaxCaterpillar.Max5Optimal.ConvexCores.Check
