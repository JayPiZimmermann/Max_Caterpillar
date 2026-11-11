import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConditionalBound
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.GeneralRowsCoverage
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.GeneralRowsEnvelope

/-! # Explicit conditional general-row lower bound with integer parameters

The normalized actual network computes MAX_n. The only structural premise is
H(4q+1,q). All side conditions, coverage and per-neuron estimates are proved
from d,q and the two displayed integer size hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators Parameters
variable {h₁ h₂ : ℕ}

local instance arityNeZero (q : ℕ) : NeZero (braidArity q) :=
  ⟨Nat.ne_of_gt (Nat.succ_pos (4*q))⟩
local instance generalTotalNeZero (m q : ℕ) : NeZero (m+braidArity q) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos (4*q)) (Nat.le_add_left _ m))⟩

private theorem total_pos (n d : ℕ) (hd : 1≤d) (hn : 8000*d^2≤n) : 0<n := by
  have hh : 1≤d^2 := by nlinarith only [hd]
  nlinarith only [hn,hh]

/-- Tail-indexed version, convenient for the actual finite transfer. -/
theorem conditional_general_rows_of_tail (m d q : ℕ) (hd : 1≤d) (hq : 1≤q)
    (hn : 8000*d^2≤m+braidArity q) (hcube : 1000*d^2*q^3≤m+braidArity q)
    (H : LocalMatchingObstruction (braidArity q) q)
    (net : NormalizedNetwork (m+braidArity q) h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+braidArity q) x)
    (hM : (BadFirst.largeSupportCount (firstSupports net) : ℝ)≤
      (d : ℝ)^2*((m+braidArity q : ℕ) : ℝ)^2)
    (hL : (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ))≤
      (d : ℝ)^2*((m+braidArity q : ℕ) : ℝ)^2) :
    (1/2 : ℝ)*(((m+braidArity q : ℕ) : ℝ)/(400000*(d : ℝ)*(q : ℝ)^2))^q ≤ (h₂ : ℝ) := by
  let n := m+braidArity q
  let K := m/(1000*d)
  have hb := general_row_parameter_bounds n d q hd hq hn hcube
  have htail : braidTail n q=m := Nat.add_sub_cancel_right m (braidArity q)
  have hm400 : 400≤m := by simpa only [htail] using hb.tail_four_hundred
  have hKfour : 4≤K := by simpa only [generalRanks,htail] using hb.ranks_lower
  have hKlt : K<m := by simpa only [generalRanks,htail] using hb.ranks_lt_tail
  letI : NeZero (braidArity q) := ⟨Nat.ne_of_gt hb.arity_pos⟩
  have ht := conditional_finite_transfer H (lt_of_lt_of_le (by decide : 0<1) hq)
    net hnorm hnet K ((by decide : 2≤400).trans hm400)
    ((by decide : 4≤8000).trans hb.total_lower) hKfour hKlt
  have hcoverage := general_row_coverage n d q hd hq hn hcube
    (BadFirst.largeSupportCount (firstSupports net) : ℝ)
    (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ)) hM hL
  have henvelope := general_row_envelope n d q hd hq hn hcube
  have hc : (1/2 : ℝ) ≤ (h₂ : ℝ)*perNeuronEnvelope m (braidArity q) K q := by
    have hf : _ ≤ (h₂ : ℝ)*perNeuronEnvelope m (braidArity q) K q := by
      simpa only [perNeuronEnvelope,mul_assoc] using ht
    apply le_trans _ hf
    simpa only [generalRanks,htail] using hcoverage
  have he : perNeuronEnvelope m (braidArity q) K q ≤
      (400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ))^q := by
    simpa only [generalRanks,htail] using henvelope
  have hwidth : (1/2 : ℝ) ≤ (h₂ : ℝ)*(400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ))^q :=
    hc.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))
  have hp : (0 : ℝ)<(400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ))^q := by positivity
  have hdiv : (1/2 : ℝ)/(400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ))^q ≤ (h₂ : ℝ) :=
    (div_le_iff hp).mpr (by simpa only [mul_comm] using hwidth)
  have hrecip : ((n : ℝ)/(400000*(d : ℝ)*(q : ℝ)^2))^q =
      ((400000*(d : ℝ)*(q : ℝ)^2/(n : ℝ))^q)⁻¹ := by
    rw [←inv_pow,inv_div]
  change (1/2 : ℝ)*((n : ℝ)/(400000*(d : ℝ)*(q : ℝ)^2))^q ≤ (h₂ : ℝ)
  rw [hrecip]
  exact hdiv

/-- Integer-parameter finite general-row consequence of the actual transfer.
For fixed d, q may grow near (n/(1000*d^2))^(1/3). This theorem asserts the
finite inequality; no growing structural hypothesis is silently discharged. -/
theorem conditional_general_rows (n d q : ℕ) (hd : 1≤d) (hq : 1≤q)
    (hn : 8000*d^2≤n) (hcube : 1000*d^2*q^3≤n)
    (H : LocalMatchingObstruction (braidArity q) q)
    (net : NormalizedNetwork n h₁ h₂) (hnorm : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=@Maximum n ⟨Nat.ne_of_gt (total_pos n d hd hn)⟩ x)
    (hM : (BadFirst.largeSupportCount (firstSupports (m:=n) (k:=0) net) : ℝ)≤(d : ℝ)^2*(n : ℝ)^2)
    (hL : (∑ j,((firstSupports (m:=n) (k:=0) net j).card.descFactorial 4 : ℝ))≤(d : ℝ)^2*(n : ℝ)^2) :
    (1/2 : ℝ)*((n : ℝ)/(400000*(d : ℝ)*(q : ℝ)^2))^q ≤ (h₂ : ℝ) := by
  have hb := general_row_parameter_bounds n d q hd hq hn hcube
  have hsum := hb.total_eq
  generalize hm : braidTail n q=m at hsum
  subst n
  exact conditional_general_rows_of_tail m d q hd hq hn hcube H net hnorm hnet hM hL

#print axioms conditional_general_rows_of_tail
#print axioms conditional_general_rows
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
