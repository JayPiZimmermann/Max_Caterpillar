import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConditionalBound

/-! # Explicit finite conditional exponential braid lower bound

Only the local structural obstruction H(4q+1,q) remains a hypothesis.
The actual finite transfer, its braid support statistics, every parameter
side condition and the envelope bound are derived in the proof.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
open BigOperators Parameters

instance braidArity_neZero (q : ℕ) : NeZero (braidArity q) :=
  ⟨Nat.succ_ne_zero (4*q)⟩

lemma largeSupportCount_eq_zero {n : ℕ} {κ : Type*} [Fintype κ]
    (T : κ → Finset (Fin n)) (hT : ∀ j, (T j).card ≤ 2) :
    BadFirst.largeSupportCount T = 0 := by
  classical
  unfold BadFirst.largeSupportCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro j hj
  have hl := (BadFirst.mem_largeSupportRows T j).mp hj
  have hs := hT j
  linarith only [hl,hs]

lemma support_descFactorial_four_sum_eq_zero {n : ℕ} {κ : Type*} [Fintype κ]
    (T : κ → Finset (Fin n)) (hT : ∀ j, (T j).card ≤ 2) :
    (∑ j, ((T j).card.descFactorial 4 : ℝ)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  have hs : (T j).card < 4 := lt_of_le_of_lt (hT j) (by decide : 2 < 4)
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hs,Nat.cast_zero]

/-- The ambient dimension's required typeclass is derived from the stated size hypotheses. -/
def braidDimension_neZero (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) : NeZero n :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 160000)
    (braid_parameter_bounds n q hq hsize).total_lower)⟩

/-- Finite integer-q form of the explicit conditional braid consequence (B).
The input dimension is arbitrary: k,m,K are the literal choices 4q+1,
n-k and floor((n-k)/100), not additional assumptions. -/
theorem conditional_braid_integer_q_lower_bound
    {n h₁ h₂ : ℕ} (q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n)
    (H : LocalMatchingObstruction (braidArity q) q)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : letI := braidDimension_neZero n q hq hsize; ∀ x, net.eval x = Maximum n x)
    (hbraid : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card ≤ 2) :
    (23/25:ℝ)*4^q ≤ (h₂:ℝ) := by
  have hb := braid_parameter_bounds n q hq hsize
  obtain ⟨m,heq⟩ := Nat.exists_eq_add_of_le' hb.arity_le_total
  subst n
  have htail : braidTail (m+braidArity q) q = m := by
    unfold braidTail
    exact Nat.add_sub_cancel _ _
  let K := braidRanks (m+braidArity q) q
  have hm : 2 ≤ m := by
    have hh := (by decide : 2 ≤ 400).trans hb.tail_four_hundred
    simpa only [htail] using hh
  have htotal : 4 ≤ m+braidArity q := (by decide : 4 ≤ 160000).trans hb.total_lower
  have hK : 4 ≤ K := hb.ranks_lower
  have hKm : K < m := by simpa only [htail] using hb.ranks_lt_tail
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 1) hq
  have hM := largeSupportCount_eq_zero (firstSupports net) hbraid
  have hL := support_descFactorial_four_sum_eq_zero (firstSupports net) hbraid
  have ht := conditional_finite_transfer H hqpos net hn hnet K hm htotal hK hKm
  rw [hM,hL] at ht
  simp only [Nat.cast_zero,zero_mul,zero_div,sub_zero] at ht
  have htransfer : 1-8*(K:ℝ)/(m:ℝ) ≤
      (h₂:ℝ)*perNeuronEnvelope m (braidArity q) K q := by
    simpa only [perNeuronEnvelope,mul_assoc] using ht
  have henv : perNeuronEnvelope m (braidArity q) K q ≤ (1/4:ℝ)^q := by
    simpa only [htail] using braid_envelope_le (m+braidArity q) q hq hsize
  have hupper : 100*(K:ℝ) ≤ (m:ℝ) := by
    have hh := hb.ranks_upper
    rw [htail] at hh
    exact_mod_cast hh
  have hmpos : (0:ℝ) < m := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hm
  have hcost : 8*(K:ℝ)/(m:ℝ) ≤ (2/25:ℝ) := by
    apply (div_le_iff hmpos).mpr
    linarith only [hupper]
  have hleft : (23/25:ℝ) ≤ 1-8*(K:ℝ)/(m:ℝ) := by linarith only [hcost]
  have hfinal : (23/25:ℝ) ≤ (h₂:ℝ)*(1/4:ℝ)^q :=
    hleft.trans (htransfer.trans (mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg h₂)))
  calc
    (23/25:ℝ)*4^q ≤ ((h₂:ℝ)*(1/4:ℝ)^q)*4^q :=
      mul_le_mul_of_nonneg_right hfinal (pow_nonneg (by norm_num) q)
    _ = (h₂:ℝ)*(((1/4:ℝ)*4)^q) := by rw [mul_pow]; ring
    _ = (h₂:ℝ) := by norm_num

#check @conditional_braid_integer_q_lower_bound
#print axioms conditional_braid_integer_q_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
