import Mathlib.Tactic

/-! The final linear-inequality core of the analytic natural-eight
five-free-unit obstruction. This is not a Lean formalization of the
network-to-corner reduction; that bridge is in the accompanying note. -/

namespace NaturalEightFiveCorner

/-- No two normalized forms can have the required signs or equal
restrictions on the four full corner cones. -/
theorem corner_compatibility_impossible
    (G H x s z v : ℝ)
    (corner22 : (0 ≤ s ∧ 1 ≤ v) ∨ (s ≤ -1 ∧ v ≤ 0))
    (corner02 :
      (G ≤ -1 ∧ ((0 ≤ x ∧ 1 ≤ v) ∨ (x ≤ -1 ∧ v ≤ 0))) ∨
      (x = G ∧ v = 0))
    (corner20 :
      (1 ≤ H ∧ ((0 ≤ s ∧ 1 ≤ z) ∨ (s ≤ -1 ∧ z ≤ 0))) ∨
      (s = 0 ∧ z = H))
    (corner00 :
      (((0 ≤ G ∧ 1 ≤ H) ∨ (G ≤ -1 ∧ H ≤ 0)) ∧
       ((0 ≤ x ∧ 1 ≤ z) ∨ (x ≤ -1 ∧ z ≤ 0))) ∨
      (x = G ∧ z = H)) : False := by
  rcases corner22 with ⟨hs, hv⟩ | ⟨hs, hv⟩ <;>
  rcases corner02 with ⟨hG, (⟨hx, hv'⟩ | ⟨hx, hv'⟩)⟩ | ⟨hx, hv'⟩ <;>
  rcases corner20 with ⟨hH, (⟨hs', hz⟩ | ⟨hs', hz⟩)⟩ | ⟨hs', hz⟩ <;>
  rcases corner00 with
    ⟨(⟨hG', hH'⟩ | ⟨hG', hH'⟩), (⟨hx', hz'⟩ | ⟨hx', hz'⟩)⟩ |
    ⟨hx', hz'⟩ <;> linarith

#print axioms corner_compatibility_impossible

end NaturalEightFiveCorner
