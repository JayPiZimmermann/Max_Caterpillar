import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ExpSeries

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
example (c η : ℝ) (hc : 0 < c) (hη : 0 ≤ η) (q : ℕ) :
    η ^ q * Real.exp (-(c * η)) / (q.factorial : ℝ) ≤ (c ^ q)⁻¹ :=
  pow_mul_exp_neg_div_factorial_le_inv_pow c η hc hη q
example (P A c η d : ℝ) (q : ℕ) (hc : 0 < c) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hP : P ≤ A * η ^ q / (q.factorial : ℝ) * Real.exp (-(c * (η - d)))) :
    P ≤ A * (c ^ q)⁻¹ * Real.exp (c * d) :=
  le_shifted_exp_envelope P A c η d q hc hη hA hP

-- The endpoints q=0 and eta=0 remain included.
example (c η : ℝ) (hc : 0 < c) (hη : 0 ≤ η) : Real.exp (-(c * η)) ≤ 1 := by
  simpa using pow_mul_exp_neg_div_factorial_le_inv_pow c η hc hη 0
example (c : ℝ) (hc : 0 < c) (q : ℕ) :
    (0 : ℝ)^q * Real.exp (-(c * 0)) / (q.factorial : ℝ) ≤ (c ^ q)⁻¹ :=
  pow_mul_exp_neg_div_factorial_le_inv_pow c 0 hc (le_refl 0) q

#check @pow_mul_exp_neg_div_factorial_le_inv_pow
#check @le_shifted_exp_envelope
#print axioms pow_mul_exp_neg_div_factorial_le_inv_pow
#print axioms le_shifted_exp_envelope
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
