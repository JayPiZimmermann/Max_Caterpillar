import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GeneralRows

set_option autoImplicit false
namespace GeneralRowsCheck
open BigOperators
open MaxCaterpillar MaxCaterpillar.Frontier MaxCaterpillar.Frontier.RandomRestriction
open GrowingMatching GrowingMatching.Parameters
variable {h₁ h₂ : ℕ}

/-- All integer floor and arity requirements follow from the size hypotheses. -/
example (n d q : ℕ) (hd : 1≤d) (hq : 1≤q)
    (hn : 8000*d^2≤n) (hc : 1000*d^2*q^3≤n) :
    4≤(n-(4*q+1))/(1000*d) ∧ (n-(4*q+1))/(1000*d)<n-(4*q+1) ∧
      n≤4000*d*((n-(4*q+1))/(1000*d)) ∧
      n-(4*q+1)+(4*q+1)=n ∧ 400≤n-(4*q+1) := by
  have hb := general_row_parameter_bounds n d q hd hq hn hc
  exact ⟨hb.ranks_lower,hb.ranks_lt_tail,hb.ranks_lower_total,hb.total_eq,hb.tail_four_hundred⟩

/-- Expected actual-network type: structural H, normalization and exact MAX,
plus two original-row budgets. No probability or scalar-envelope premise. -/
example (n d q : ℕ) [NeZero n] (hd : 1≤d) (hq : 1≤q)
    (hn : 8000*d^2≤n) (hc : 1000*d^2*q^3≤n)
    (H : LocalMatchingObstruction (4*q+1) q)
    (net : NormalizedNetwork n h₁ h₂) (hNorm : net.TranslationNormalized)
    (hMax : ∀ x, net.eval x=Maximum n x)
    (hM : (GrowingMatching.BadFirst.largeSupportCount (GrowingMatching.firstSupports (m:=n) (k:=0) net) : ℝ)≤
      (d : ℝ)^2*(n : ℝ)^2)
    (hL : (∑ j,((GrowingMatching.firstSupports (m:=n) (k:=0) net j).card.descFactorial 4 : ℝ))≤
      (d : ℝ)^2*(n : ℝ)^2) :
    (1/2 : ℝ)*((n : ℝ)/(400000*(d : ℝ)*(q : ℝ)^2))^q≤(h₂ : ℝ) :=
  conditional_general_rows n d q hd hq hn hc H net hNorm hMax hM hL

/-- Positive boundary data: the cubic inequality is attained at d=1,q=2,n=8000. -/
example : 8000*1^2≤8000 ∧ 1000*1^2*2^3≤8000 := by norm_num
example : braidArity 2=9 := rfl
example : braidTail 8000 2=7991 := rfl
example : generalRanks 8000 1 2=7 := rfl

example : ¬1000*1^2*3^3≤8000 := by norm_num

/-- The coverage proof accepts positive row counts and positive falling moments. -/
example : (1/2 : ℝ)≤1-8*(generalRanks 8000 1 2 : ℝ)/(braidTail 8000 2 : ℝ)-
    64000000*((braidArity 2).descFactorial 3 : ℝ)/((8000 : ℕ).descFactorial 3 : ℝ)-
    64000000/((8000 : ℕ).descFactorial 4 : ℝ)*
      ((generalRanks 8000 1 2 : ℝ)^2*(1+(braidArity 2 : ℝ)/(braidTail 8000 2 : ℝ))/
        (1-(generalRanks 8000 1 2 : ℝ)/(braidTail 8000 2 : ℝ))+
        ((braidArity 2).descFactorial 2 : ℝ)*(generalRanks 8000 1 2 : ℝ)/2) :=
  general_row_coverage 8000 1 2 (by decide) (by decide) (by decide) (by decide)
    64000000 64000000 (by norm_num) (by norm_num)

example : perNeuronEnvelope 7991 9 7 2≤(400000*(1 : ℝ)*2^2/8000)^2 := by
  simpa only [show braidTail 8000 2=7991 from rfl,show braidArity 2=9 from rfl,
    show generalRanks 8000 1 2=7 from rfl,Nat.cast_one,Nat.cast_ofNat] using
      general_row_envelope 8000 1 2 (by decide) (by decide) (by decide) (by decide)

/-- A nontrivial parameter instance: the actual per-neuron factor is at most 1/4. -/
example : perNeuronEnvelope (braidTail 3200000 2) (braidArity 2)
    (generalRanks 3200000 1 2) 2≤(1/4 : ℝ) := by
  have he := general_row_envelope 3200000 1 2 (by decide) (by decide) (by norm_num) (by norm_num)
  convert he using 1 <;> norm_num

#print axioms general_row_parameter_bounds
#print axioms descFactorial_three_lower
#print axioms descFactorial_four_lower
#print axioms general_row_coverage
#print axioms general_row_envelope
#print axioms conditional_general_rows_of_tail
#print axioms conditional_general_rows
end GeneralRowsCheck
