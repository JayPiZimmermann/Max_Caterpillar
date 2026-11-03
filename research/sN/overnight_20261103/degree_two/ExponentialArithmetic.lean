import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Elementary arithmetic turning the exact selected-set estimate into an
explicit exponential lower bound. The exact binomial form remains sharper. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators

theorem pow_two_le_middle_choose (N : ℕ) :
    2^N ≤ (N+1)*N.choose (N/2) := by
  calc
    2^N = ∑ k in Finset.range (N+1),N.choose k := (Nat.sum_range_choose N).symm
    _ ≤ ∑ _k in Finset.range (N+1),N.choose (N/2) :=
      Finset.sum_le_sum (fun k _ => Nat.choose_le_middle k N)
    _ = (N+1)*N.choose (N/2) := by simp

theorem middle_capacity_le_cube (N : ℕ) (hN : 2≤N) :
    2*N+2*(N/2-1)*N^2 ≤ N^3 := by
  have hhalf : 1≤N/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hN
  have hs : 2*(N/2-1)+2≤N := by omega
  have hNsq : N≤N^2 := by
    simpa only [pow_two,one_mul] using Nat.mul_le_mul_right N (show 1≤N by omega)
  have hp := Nat.mul_le_mul_right (N^2) hs
  calc
    2*N+2*(N/2-1)*N^2 ≤ 2*N^2+2*(N/2-1)*N^2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hNsq) _
    _ = (2*(N/2-1)+2)*N^2 := by ring
    _ ≤ N*N^2 := hp
    _ = N^3 := by ring

theorem pow_two_le_width_polynomial (N h₂ : ℕ) (hN : 6≤N)
    (hbin : N.choose (N/2)≤h₂*(2*N+2*(N/2-1)*N^2)) :
    2^N ≤ h₂*(N^3*(N+1)) := by
  have hcap := middle_capacity_le_cube N (by omega)
  have hwidth := hbin.trans (Nat.mul_le_mul_left h₂ hcap)
  calc
    2^N ≤ (N+1)*N.choose (N/2) := pow_two_le_middle_choose N
    _ ≤ (N+1)*(h₂*N^3) := Nat.mul_le_mul_left (N+1) hwidth
    _ = h₂*(N^3*(N+1)) := by ring

#check @pow_two_le_width_polynomial
#print axioms pow_two_le_middle_choose
#print axioms middle_capacity_le_cube
#print axioms pow_two_le_width_polynomial
end MaxCaterpillar.Overnight.DegreeTwo
