import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphQuadratic
import MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavingsNative

/-! # Actual real quadratic matrices supported on the fixed triangle

Diagonal terms enter the effective linear coefficients. Opposite ordered
matrix entries enter only through their sum, including exact cancellation.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
open BigOperators

/-- Support of the actual interaction graph controls the summed ordered
coefficient, without imposing any condition on either matrix entry alone. -/
theorem effectiveInteraction_zero_outside_fixed_triangle
    (d : Fin 5 → Fin 5 → ℝ)
    (hsupport : ∀ i j,(quadraticInteractionGraph d).Adj i j → i.val<3 ∧ j.val<3)
    (i j : Fin 5) (hij : i≠j) (hout : 3≤i.val ∨ 3≤j.val) :
    effectiveInteraction d i j=0 := by
  by_contra hn
  have h := hsupport i j ⟨hij,hn⟩
  rcases hout with hi | hj
  · exact (Nat.not_lt.mpr hi) h.1
  · exact (Nat.not_lt.mpr hj) h.2

/-- The unrestricted ordered real quadratic model has the eight-coefficient
native triangle form whenever its actual graph is supported on vertices 012. -/
theorem booleanQuadratic_eq_nativeTriangle_fixed (a : ℝ) (b : Fin 5 → ℝ)
    (d : Fin 5 → Fin 5 → ℝ)
    (hsupport : ∀ i j,(quadraticInteractionGraph d).Adj i j → i.val<3 ∧ j.val<3)
    (ha : a=0) :
    booleanQuadratic a b d=TriangleInterleavings.nativeTriangle
      ![effectiveLinear b d 0,effectiveLinear b d 1,effectiveLinear b d 2,
        effectiveInteraction d 0 1,effectiveInteraction d 0 2,effectiveInteraction d 1 2,
        effectiveLinear b d 3,effectiveLinear b d 4] := by
  subst a
  have h03 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 0 3
    (by decide) (Or.inr (by decide))
  have h04 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 0 4
    (by decide) (Or.inr (by decide))
  have h13 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 1 3
    (by decide) (Or.inr (by decide))
  have h14 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 1 4
    (by decide) (Or.inr (by decide))
  have h23 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 2 3
    (by decide) (Or.inr (by decide))
  have h24 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 2 4
    (by decide) (Or.inr (by decide))
  have h34 := effectiveInteraction_zero_outside_fixed_triangle d hsupport 3 4
    (by decide) (Or.inr (by decide))
  funext B
  rw [TriangleInterleavings.nativeTriangle_formula]
  have hcoordinate : ∀ i,TriangleInterleavings.coordinate B i=booleanCoordinate i B :=
    fun _ => rfl
  simp only [hcoordinate]
  unfold booleanQuadratic effectiveLinear effectiveInteraction
  simp only [Fin.sum_univ_five,booleanCoordinate_square,zero_add]
  unfold effectiveInteraction at h03 h04 h13 h14 h23 h24 h34
  linear_combination (booleanCoordinate 0 B*booleanCoordinate 3 B)*h03+
    (booleanCoordinate 0 B*booleanCoordinate 4 B)*h04+
    (booleanCoordinate 1 B*booleanCoordinate 3 B)*h13+
    (booleanCoordinate 1 B*booleanCoordinate 4 B)*h14+
    (booleanCoordinate 2 B*booleanCoordinate 3 B)*h23+
    (booleanCoordinate 2 B*booleanCoordinate 4 B)*h24+
    (booleanCoordinate 3 B*booleanCoordinate 4 B)*h34

/-- The empty-set normalization supplies the zero constant required above. -/
theorem booleanQuadratic_eq_nativeTriangle_fixed_of_empty
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (hsupport : ∀ i j,(quadraticInteractionGraph d).Adj i j → i.val<3 ∧ j.val<3)
    (hEmpty : booleanQuadratic a b d ∅=0) :
    booleanQuadratic a b d=TriangleInterleavings.nativeTriangle
      ![effectiveLinear b d 0,effectiveLinear b d 1,effectiveLinear b d 2,
        effectiveInteraction d 0 1,effectiveInteraction d 0 2,effectiveInteraction d 1 2,
        effectiveLinear b d 3,effectiveLinear b d 4] := by
  have ha : a=0 := by simpa [booleanQuadratic,booleanCoordinate] using hEmpty
  exact booleanQuadratic_eq_nativeTriangle_fixed a b d hsupport ha

/-- Full-set normalization imposes precisely the sum-zero coefficient equation. -/
theorem fixed_triangle_coefficients_sum_zero
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (hsupport : ∀ i j,(quadraticInteractionGraph d).Adj i j → i.val<3 ∧ j.val<3)
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    effectiveLinear b d 0+effectiveLinear b d 1+effectiveLinear b d 2+
      effectiveInteraction d 0 1+effectiveInteraction d 0 2+effectiveInteraction d 1 2+
      effectiveLinear b d 3+effectiveLinear b d 4=0 := by
  rw [booleanQuadratic_eq_nativeTriangle_fixed_of_empty a b d hsupport hEmpty,
    TriangleInterleavings.nativeTriangle_full] at hFull
  exact hFull

end MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
