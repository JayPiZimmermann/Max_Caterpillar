import research.sN.overnight_20261103.constants.tradeoff.ScalarMin
import research.sN.overnight_20261103.constants.tradeoff_theta.FeedingScaled

/-! The improved minimum tradeoff counts only original first neurons that
feed the second hidden layer. Output-only first neurons are unrestricted. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta.Feeding
open Frontier Frontier.RandomRestriction AffineSkipExtension FeedingCore
variable {N h₁ h₂ : ℕ}

theorem affine_min_tradeoff (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    min ((N:ℝ)^2) ((N:ℝ)^4/(affineFeedingCard net:ℝ))/175000≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hNpos : (0:ℝ)<N := by linarith only [hNr]
  have hh := Tradeoff.min_tradeoff_of_scaled ((N:ℝ)^2) (affineFeedingCard net:ℝ) (h₂:ℝ) 175000
    (pow_pos hNpos 2) (by norm_num)
    (fun C hC hw => affine_scaled hN net C hC hnet hw)
  have heq : ((N:ℝ)^2)^2=(N:ℝ)^4 := by ring
  rwa [heq] at hh

/-- No cap is placed on first neurons feeding only the output. -/
theorem affine_quadratic_of_feeding_cap (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (affineFeedingCard net:ℝ)≤(N:ℝ)^2 → (N:ℝ)^2/175000≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet hw
  simpa only [mul_one,one_mul] using affine_scaled hN net 1 le_rfl hnet (by simpa using hw)

#check @affine_min_tradeoff
#print axioms affine_min_tradeoff
#print axioms affine_quadratic_of_feeding_cap
end MaxCaterpillar.OvernightConstants.TradeoffTheta.Feeding
