import research.sN.overnight_20261103.degree_two.ExponentialArithmetic

/-! Preserve the fourfold constant improvement from the two-dart count
when passing to an elementary exponential estimate. -/
set_option autoImplicit false
namespace MaxCaterpillar.Overnight.DegreeTwo

theorem double_sharp_middle_capacity_le_cube (N : ℕ) (hN : 2≤N) :
    2*(2*N+(N/2-1)*N^2)≤N^3 := by
  have hhalf : 1≤N/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hN
  have hs : 2*(N/2-1)+2≤N := by
    calc
      2*(N/2-1)+2 = 2*((N/2-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = 2*(N/2) := by rw [Nat.sub_add_cancel hhalf]
      _ ≤ N := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self N 2
  have hNsq : 2*N≤N^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right N hN
  calc
    2*(2*N+(N/2-1)*N^2) = 2*(2*N)+2*((N/2-1)*N^2) := Nat.mul_add _ _ _
    _ ≤ 2*N^2+2*((N/2-1)*N^2) := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hNsq) _
    _ = (2*(N/2-1)+2)*N^2 := by
      simp only [Nat.add_mul,Nat.mul_assoc]
      exact Nat.add_comm _ _
    _ ≤ N*N^2 := Nat.mul_le_mul_right (N^2) hs
    _ = N^3 := (pow_succ N 2).symm

/-- The elementary power bound retains the sharp capacity constant. -/
theorem four_pow_two_le_width_polynomial (N h₂ : ℕ) (hN : 2≤N)
    (hbin : 2*N.choose (N/2)≤h₂*(2*N+(N/2-1)*N^2)) :
    4*2^N≤h₂*(N^3*(N+1)) := by
  have hcap := double_sharp_middle_capacity_le_cube N hN
  have hwidth : 4*N.choose (N/2)≤h₂*N^3 := by
    calc
      4*N.choose (N/2) = 2*(2*N.choose (N/2)) := by rw [←Nat.mul_assoc]
      _ ≤ 2*(h₂*(2*N+(N/2-1)*N^2)) := Nat.mul_le_mul_left 2 hbin
      _ = h₂*(2*(2*N+(N/2-1)*N^2)) := by ac_rfl
      _ ≤ h₂*N^3 := Nat.mul_le_mul_left h₂ hcap
  calc
    4*2^N ≤ 4*((N+1)*N.choose (N/2)) := Nat.mul_le_mul_left 4 (pow_two_le_middle_choose N)
    _ = (N+1)*(4*N.choose (N/2)) := by ac_rfl
    _ ≤ (N+1)*(h₂*N^3) := Nat.mul_le_mul_left (N+1) hwidth
    _ = h₂*(N^3*(N+1)) := by ac_rfl

#check @four_pow_two_le_width_polynomial
#print axioms double_sharp_middle_capacity_le_cube
#print axioms four_pow_two_le_width_polynomial
end MaxCaterpillar.Overnight.DegreeTwo
