import MaxCaterpillar.Fiber.Count65.RootFrames
import MaxCaterpillar.Fiber.First65.TwoRootGeometry

/-! # Exact positive normalization of two-support covectors

No finite coefficient alphabet is involved: every nonzero zero-sum covector
with support two is a positive multiple of one ordered coordinate difference.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier RootFrames

/-- The root direction includes its orientation; its real magnitude stays free. -/
theorem positive_root_of_support_two (a : Point 4) (hsum : ∑ i, a i = 0)
    (hcard : (nonzeroCoordinates a).card = 2) :
    ∃ p : Root, p.1 ≠ p.2 ∧ ∃ c : ℝ, 0 < c ∧ a = c • row p := by
  classical
  obtain ⟨p, q, hpq, hsupp⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨hp, hform⟩ := eq_coordinate_difference_of_support_pair a hsum p q hpq hsupp
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · refine ⟨(q,p), hpq.symm, -a p, neg_pos.mpr hneg, ?_⟩
    funext i
    change a i = (-a p) * ((if i = q then 1 else 0) - (if i = p then 1 else 0))
    rw [hform i]
    ring
  · refine ⟨(p,q), hpq, a p, hpos, ?_⟩
    funext i
    change a i = a p * ((if i = p then 1 else 0) - (if i = q then 1 else 0))
    rw [hform i]
    ring

/-- Positive multiples of proper coordinate differences have exactly two
nonzero coordinates. -/
theorem support_two_of_positive_root (p : Root) (hp : p.1 ≠ p.2)
    (c : ℝ) (hc : 0 < c) :
    (nonzeroCoordinates (c • row p)).card = 2 := by
  classical
  have hs : nonzeroCoordinates (c • row p) = {p.1, p.2} := by
    apply Finset.ext
    intro i
    rw [mem_nonzeroCoordinates]
    change c * row p i ≠ 0 ↔ _
    rw [mul_ne_zero_iff]
    have hc0 : c ≠ 0 := ne_of_gt hc
    simp only [hc0, true_and, Finset.mem_insert, Finset.mem_singleton]
    have hz := row_zero_iff p hp i
    tauto
  rw [hs]
  simp [hp]

#print axioms positive_root_of_support_two
end MaxCaterpillar.Fiber.Count65
