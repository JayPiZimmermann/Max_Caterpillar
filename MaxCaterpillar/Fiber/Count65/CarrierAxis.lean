import MaxCaterpillar.Fiber.First65.LocalMixed

/-! # An inactive invariant state forces the carrier onto the winning axis

A single test point suffices. Translation along the diagonal switches off all
rows of the wrong slope sign. The first-state kernel obstruction then forces
the sole remaining carrier to read precisely the winning coordinate.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators Filter Topology MaxCaterpillar.Frontier

/-- A generic signed diagonal direction isolates a carrier. Biases are arbitrary
in the original exact network; the first-state obstruction uses recession. -/
theorem carrier_axis_of_inactive_invariants {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (p : Fin 6) (i : Fin 4)
    (q : Point 4) (hq : q i = Maximum 4 q) (δ : ℝ) (hδ : δ ≠ 0)
    (hslope : ∀ j, j ≠ p → δ * (∑ k, net.W₁ j k) ≤ 0)
    (hinactive : ∀ j, (∑ k, net.W₁ j k) = 0 → lin (net.W₁ j) q < 0) :
    ∀ k, k ≠ i → net.W₁ p k = 0 := by
  classical
  have hevent : ∀ j : Fin 6, ∀ᶠ t : ℝ in atTop,
      j ≠ p → lin (net.W₁ j) (q + diag (δ * t)) < 0 := by
    intro j
    by_cases hj : j = p
    · exact Filter.eventually_of_forall fun _ h => (h hj).elim
    · have hs := hslope j hj
      rcases lt_or_eq_of_le hs with hs | hs
      · filter_upwards [eventually_gt_atTop
          (lin (net.W₁ j) q / (-(δ * ∑ k, net.W₁ j k)))] with t ht
        intro _
        have ht' := (div_lt_iff (neg_pos.mpr hs)).mp ht
        rw [lin_add_right, lin_diag]
        nlinarith only [ht']
      · have hzero : (∑ k, net.W₁ j k) = 0 :=
          (mul_eq_zero.mp hs).resolve_left hδ
        exact Filter.eventually_of_forall fun t _ => by
          rw [lin_add_right, lin_diag, hzero, mul_zero, add_zero]
          exact hinactive j hzero
  obtain ⟨t, ht⟩ := (Filter.eventually_all.mpr hevent).exists
  have hwinner : ((q + diag (δ * t)) : Point 4) i = Maximum 4 (q + diag (δ * t)) := by
    rw [Maximum_add_diag]
    change q i + δ * t = Maximum 4 q + δ * t
    rw [hq]
  apply Mixed65.row_support_of_single_active net hnet (q + diag (δ * t)) p i
  · intro j hj
    apply ht j
    simpa only [Finset.mem_singleton] using hj
  · exact hwinner

/-- The positive-diagonal version. -/
theorem positive_carrier_axis_of_inactive_invariants {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (p : Fin 6) (i : Fin 4)
    (q : Point 4) (hq : q i = Maximum 4 q)
    (hunique : ∀ j, 0 < ∑ k, net.W₁ j k → j = p)
    (hinactive : ∀ j, (∑ k, net.W₁ j k) = 0 → lin (net.W₁ j) q < 0) :
    ∀ k, k ≠ i → net.W₁ p k = 0 := by
  apply carrier_axis_of_inactive_invariants net hnet p i q hq 1 one_ne_zero _ hinactive
  intro j hj
  rw [one_mul]
  exact le_of_not_gt (fun h => hj (hunique j h))

/-- The negative-diagonal version. -/
theorem negative_carrier_axis_of_inactive_invariants {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (p : Fin 6) (i : Fin 4)
    (q : Point 4) (hq : q i = Maximum 4 q)
    (hunique : ∀ j, (∑ k, net.W₁ j k) < 0 → j = p)
    (hinactive : ∀ j, (∑ k, net.W₁ j k) = 0 → lin (net.W₁ j) q < 0) :
    ∀ k, k ≠ i → net.W₁ p k = 0 := by
  apply carrier_axis_of_inactive_invariants net hnet p i q hq (-1) (by norm_num) _ hinactive
  intro j hj
  have hs : 0 ≤ ∑ k, net.W₁ j k :=
    le_of_not_gt (fun h => hj (hunique j h))
  nlinarith only [hs]

#print axioms carrier_axis_of_inactive_invariants
end MaxCaterpillar.Fiber.Count65
