import MaxCaterpillar.Frontier.GeneralN
import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction

/-! # Actual-network and arbitrary-parity scalar inputs for the final tradeoff -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
variable {N n h₁ h₂ : ℕ}

lemma half_arity_ge (hN : 1040≤N) : 520≤N/2 :=
  (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hN

lemma half_arity_rounding (N : ℕ) : N≤2*(N/2)+1 := by
  have hr := Nat.mod_lt N (by decide : 0<2)
  have he := Nat.mod_add_div N 2
  linarith only [hr,he]

lemma half_arity_ge_real (hN : 1040≤N) : (520 : ℝ)≤(N/2 : ℕ) := by
  exact_mod_cast half_arity_ge hN

lemma half_arity_rounding_real (N : ℕ) : (N : ℝ)≤2*(N/2 : ℕ)+1 := by
  exact_mod_cast half_arity_rounding N

lemma half_arity_three_real (hN : 1040≤N) : (N : ℝ)≤3*(N/2 : ℕ) := by
  have hn := half_arity_ge_real hN
  have hr := half_arity_rounding_real N
  linarith only [hn,hr]

lemma tail_arity_ge_four_hundred (hn : 520≤n) : 400≤n-5 := by
  have h5 : 5≤n := (by decide : 5≤520).trans hn
  have he := Nat.sub_add_cancel h5
  linarith only [hn,he]

lemma tail_arity_cast (hn : 520≤n) : ((n-5 : ℕ) : ℝ)=(n : ℝ)-5 :=
  Nat.cast_sub ((by decide : 5≤520).trans hn)

/-- The original arbitrary-bias network already provides the positive second
width required by the scalar optimizer; no model-width replacement is used. -/
lemma actual_second_width_ge_one [NeZero N] (hN : 1040≤N)
    (net : Network N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x) :
    (1 : ℝ)≤h₂ := by
  have hw := second_width_half net hnet
  have hnat : 1≤h₂ := by linarith only [hN,hw]
  exact_mod_cast hnat

#print axioms half_arity_ge
#print axioms half_arity_rounding
#print axioms actual_second_width_ge_one
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
