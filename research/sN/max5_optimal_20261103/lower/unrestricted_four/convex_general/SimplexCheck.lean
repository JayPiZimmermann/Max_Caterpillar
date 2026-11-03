import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.ContactMaximum

/-! Literal-type consumers for the translated contact geometry. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Frontier
open Filter Topology Frontier.RandomRestriction.NormalizedNetwork

example {N : ℕ} [NeZero N] (f : Point N → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hz : ∀ M s : ℝ, 0 < s → ∀ i : Fin N,
      f (fun j => M - if j = i then s else 0) = 0) :
    ∀ x, f x ≤ 0 :=
  convex_nonpos_of_contact_zeros hf hz

example : ConvexOn ℝ Set.univ (fun _ : Point 5 => (0 : ℝ)) ∧
    (∀ M s : ℝ, 0 < s → ∀ i : Fin 5,
      (fun _ : Point 5 => (0 : ℝ)) (contactVertex M s i) = 0) :=
  ⟨convexOn_const 0 convex_univ, fun _ _ _ _ => rfl⟩

example (e : Fin 4 ↪ Fin 5) (q : Point 5) (M : ℝ)
    (hq : ∀ a, q (e a) = M)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < M) (x : Point 4) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Maximum 5 (q + ε • lift e x) = M + ε * Maximum 4 x :=
  eventually_tied_Maximum_at_level e q M hq hneg x

end MaxCaterpillar.Max5Optimal.ConvexCores
