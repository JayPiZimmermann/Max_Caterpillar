import MaxCaterpillar.Dimension

open MaxCaterpillar MaxCaterpillar.Dimension

example : type_of% @exists_descent =
    (∀ {r : ℕ} {g : Equiv.Perm (Fin (r + 1 + 1))}, g 0 = 0 → g ≠ 1 →
      ∃ j : Fin r, g j.succ.succ < g j.castSucc.succ) := rfl

example : type_of% @detector_self =
    (∀ {r : ℕ} (hr : 1 ≤ r) (ρ : PathIdx r), detector ρ (pathUnit hr ρ.1) = 1) := rfl

example : type_of% @detector_other =
    (∀ {r : ℕ} (hr : 1 ≤ r) {π ρ : PathIdx r}, π ≠ ρ →
      detector ρ (pathUnit hr π.1) = 0) := rfl

example : type_of% @factorial_le_quotientDim =
    (∀ (r : ℕ), 1 ≤ r → r.factorial ≤ quotientDim r) := rfl

#print axioms exists_descent
#print axioms detector_self
#print axioms detector_other
#print axioms factorial_le_quotientDim
