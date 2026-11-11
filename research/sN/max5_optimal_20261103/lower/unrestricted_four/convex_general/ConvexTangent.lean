import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Model

/-! Convexity of an exact one-sided tangent, including every zero plateau.
No differentiability assumption or choice of a generic direction is needed. -/

set_option autoImplicit false

namespace MaxCaterpillar.Max5Optimal.ConvexCores

open BigOperators Filter Topology Frontier
open Frontier.RandomRestriction.NormalizedNetwork

variable {N m : ℕ}

lemma lift_add_smul (e : Fin m ↪ Fin N) (x y : Point m) (a b : ℝ) :
    lift e (a • x + b • y) = a • lift e x + b • lift e y := by
  funext i
  simp only [lift, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact positive-step tangents of globally convex functions are convex. -/
theorem convex_of_exact_tangent (f : Point N → ℝ) (q : Point N)
    (e : Fin m ↪ Fin N) (D : Point m → ℝ)
    (ht : ∀ x, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f (q + ε • lift e x) = f q + ε * D x)
    (hf : ConvexOn ℝ Set.univ f) : ConvexOn ℝ Set.univ D := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hx, hy, hxy⟩ :=
    (hp.and ((ht x).and ((ht y).and (ht (a • x + b • y))))).exists
  have he : a • (q + ε • lift e x) + b • (q + ε • lift e y) =
      q + ε • lift e (a • x + b • y) := by
    rw [lift_add_smul]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * (q i + ε * lift e x i) + b * (q i + ε * lift e y i) =
          (a + b) * q i + ε * (a * lift e x i + b * lift e y i) := by ring
      _ = q i + ε * (a * lift e x i + b * lift e y i) := by rw [hab, one_mul]
  have hi := hf.2 (Set.mem_univ (q + ε • lift e x))
    (Set.mem_univ (q + ε • lift e y)) ha hb hab
  rw [he, hxy, hx, hy] at hi
  simp only [smul_eq_mul] at hi ⊢
  have hs : a * (f q + ε * D x) + b * (f q + ε * D y) =
      f q + ε * (a * D x + b * D y) := by
    calc
      _ = (a + b) * f q + ε * (a * D x + b * D y) := by ring
      _ = _ := by rw [hab, one_mul]
  rw [hs] at hi
  exact (mul_le_mul_left hε).mp ((add_le_add_iff_left (f q)).mp hi)

theorem ExactTangent.convex {f : Point N → ℝ} {q : Point N}
    {e : Fin m ↪ Fin N} {D : Point m → ℝ} (ht : ExactTangent f q e D)
    (hf : ConvexOn ℝ Set.univ f) : ConvexOn ℝ Set.univ D :=
  convex_of_exact_tangent f q e D ht hf

#check @convex_of_exact_tangent
#print axioms convex_of_exact_tangent
#check @ExactTangent.convex
#print axioms ExactTangent.convex

end MaxCaterpillar.Max5Optimal.ConvexCores
