import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Falling

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
variable {m k K q : ℕ}

example (hqk : 2*q ≤ k) : m^(2*q) ≤ (m+k).descFactorial (2*q) :=
  tail_pow_le_descFactorial hqk
example (hm : 2 ≤ m) (hK : 0 < K) (hqk : 2*q ≤ k) :
    ((k.descFactorial (2*q) : ℝ) / ((m+k).descFactorial (2*q) : ℝ)) *
        ((tailRate m K)^q)⁻¹ ≤ (24*(k : ℝ)^2/(7*(K : ℝ)))^q :=
  falling_tail_envelope_le hm hK hqk
example (hm : 2 ≤ m) (hK : 0 < K) :
    ((k.descFactorial 0 : ℝ) / ((m+k).descFactorial 0 : ℝ)) *
        ((tailRate m K)^0)⁻¹ ≤ (24*(k : ℝ)^2/(7*(K : ℝ)))^0 :=
  falling_tail_envelope_le (q := 0) hm hK (Nat.zero_le _)

#check @tail_pow_le_descFactorial
#check @falling_tail_envelope_le
#print axioms tail_pow_le_descFactorial
#print axioms falling_tail_envelope_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
