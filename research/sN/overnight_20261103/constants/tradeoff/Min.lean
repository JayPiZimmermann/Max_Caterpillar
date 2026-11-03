import research.sN.overnight_20261103.constants.tradeoff.ScalarMin
import research.sN.overnight_20261103.constants.tradeoff.Scaled

/-! An unconditional width tradeoff without any upper bound on the total
first hidden width. The denominator counts the original first hidden slots. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.Tradeoff
open Frontier Frontier.RandomRestriction AffineSkipExtension
variable {N h₁ h₂ : ℕ}

/-- Every exact raw affine-skip MAX network satisfies the minimum tradeoff.
In particular no h₁=O(N²) premise is needed. -/
theorem affine_min_tradeoff (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    min ((N:ℝ)^2) ((N:ℝ)^4/(h₁:ℝ))/650000≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hNpos : (0:ℝ)<N := by linarith only [hNr]
  have hh := min_tradeoff_of_scaled ((N:ℝ)^2) (h₁:ℝ) (h₂:ℝ) 650000
    (pow_pos hNpos 2) (by norm_num)
    (fun C hC hw => affine_scaled hN net C hC hnet hw)
  have heq : ((N:ℝ)^2)^2=(N:ℝ)^4 := by ring
  rwa [heq] at hh

/-- A numerical quadratic cap is just a special case of the uncapped tradeoff. -/
theorem affine_quadratic_of_first_cap (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (h₁:ℝ)≤(N:ℝ)^2 → (N:ℝ)^2/650000≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet hw
  simpa only [mul_one,one_mul] using affine_scaled hN net 1 le_rfl hnet (by simpa using hw)

#check @affine_min_tradeoff
#print axioms affine_min_tradeoff
#print axioms affine_quadratic_of_first_cap
end MaxCaterpillar.OvernightConstants.Tradeoff
