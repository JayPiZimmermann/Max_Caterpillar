import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open Parameters

example {m k K q : ℕ} (hm : 2 ≤ m) (hK : 0 < K) (hqk : 2*q ≤ k)
    (hKupper : 100*K ≤ m) (hshape : m+k+2 ≤ 3*m) (hkq : k ≤ 5*q) :
    ((k.descFactorial (2*q):ℝ)/((m+k).descFactorial (2*q):ℝ))*
      ((tailRate m K)^q)⁻¹*
      Real.exp (tailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) ≤
      (4*(k:ℝ)^2/(K:ℝ))^q :=
  perNeuronEnvelope_le_four_sq_div_pow hm hK hqk hKupper hshape hkq

example (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    perNeuronEnvelope (braidTail n q) (braidArity q) (braidRanks n q) q ≤ (1/4:ℝ)^q :=
  braid_envelope_le n q hq hsize

-- Natural use with an ambient MAX instance agrees with the internally
-- derived positivity witness; no additional envelope assumption is supplied.
example {n h₁ h₂ : ℕ} [NeZero n] (q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n)
    (H : LocalMatchingObstruction (braidArity q) q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x = Maximum n x)
    (hbraid : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2) :
    (23/25:ℝ)*4^q ≤ (h₂:ℝ) :=
  BraidCorollary.conditional_braid_integer_q_lower_bound q hq hsize H net hn hnet hbraid

#check @braid_parameter_bounds
#check @falling_tail_envelope_le
#check @exp_shift_le
#check @perNeuronEnvelope_le_four_sq_div_pow
#check @braid_envelope_le
#check @BraidCorollary.conditional_braid_integer_q_lower_bound
#print axioms braid_parameter_bounds
#print axioms falling_tail_envelope_le
#print axioms exp_shift_le
#print axioms braid_envelope_le
#print axioms BraidCorollary.conditional_braid_integer_q_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
