import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.ConditionalBound
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

/-! # Actual conditional exponential lower bound with Bernoulli selection

The only structural premise is H at the displayed literal growing arity.
M and L below are actual support statistics, not probability assumptions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators Parameters
variable {n d h₁ h₂ : ℕ}

theorem conditional_sqrt_lower_bound [NeZero n]
    (hd : 1≤d) (hsize : 10000000000*d^2≤n)
    (H : LocalMatchingObstruction (minimumArity n d) (matchingOrder n d))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x)
    (hM : ((largeSupports (firstSupports net)).card : ℝ)≤(d : ℝ)^2*(n : ℝ)^2)
    (hL : (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ))≤(d : ℝ)^2*(n : ℝ)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt (n : ℝ)/(8000*(d : ℝ)))≤(h₂ : ℝ) := by
  classical
  have P := parameter_bounds n d hd hsize
  have hq : 0<matchingOrder n d := lt_of_lt_of_le (by decide : 0<1) P.order_pos
  have hpHalf : selectionProbability n d≤1/2 := by
    have hh := P.probability_le_thousandth
    linarith only [hh]
  have hmean : (n : ℝ)*selectionProbability n d=bernoulliMean n d := by
    rw [mul_comm,probability_mul_total n d P.n_pos hd]
  have hk : (minimumArity n d : ℝ)≤3*((n : ℝ)*selectionProbability n d)/5 := by
    rw [hmean]
    exact P.arity_upper
  have hm : 4≤n-⌊2*((n : ℝ)*selectionProbability n d)⌋₊ := by
    rw [hmean]
    exact (by decide : 4≤400).trans P.tail_lower400
  have hKm : rankCount n d<minimumTail n d := by
    have hh := P.hundred_ranks_le_tail
    have hp := P.ranks_lower
    linarith only [hh,hp]
  have hKm' : rankCount n d<n-⌊2*((n : ℝ)*selectionProbability n d)⌋₊ := by
    rw [hmean]
    exact hKm
  let M : ℝ := (largeSupports (firstSupports net)).card
  let L : ℝ := ∑ j,((firstSupports net j).card.descFactorial 4 : ℝ)
  have hL0 : 0≤L := Finset.sum_nonneg (fun _ _=>Nat.cast_nonneg _)
  have hden := admissible_denominator_pos hd hsize M hM
  have hden' : 0<Real.exp (-2*(largeSupports (firstSupports net)).card*(selectionProbability n d)^3)-
      Real.exp (-((n : ℝ)*selectionProbability n d)/3) := by
    simpa only [hmean] using hden
  have hf := finite_conditional_bound H hq net hn hnet (selectionProbability n d)
    P.probability_pos.le hpHalf (rankCount n d) hk hden' hm P.ranks_lower hKm'
  simp only [hmean] at hf
  let bsize : ℝ := Real.exp (-3*bernoulliMean n d/40)/
    (Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3))
  let bshort : ℝ := 8*(rankCount n d : ℝ)/(minimumTail n d : ℝ)
  let bgood : ℝ := L*GoodEvent.badSupportRate (selectionProbability n d) (minimumTail n d) (rankCount n d)
  have hg : bgood≤supportBudget n d L := by
    apply le_of_eq
    dsimp only [bgood,GoodEvent.badSupportRate,supportBudget]
    ring
  have hc := coverage_from_explicit_budgets hd hsize M L bsize bgood bshort hM hL0 hL
    (le_refl _) hg (le_refl _)
  change 1-bsize-bshort-bgood≤(h₂ : ℝ)*
    ((selectionProbability n d)^2/baseRate n d)^(matchingOrder n d)*
      Real.exp (baseRate n d*((selectedCap n d : ℝ)*((n : ℝ)-1))) at hf
  have hfinite : (9/10 : ℝ)≤(h₂ : ℝ)*neuronEnvelope n d := by
    have he : 1-bsize-bshort-bgood≤(h₂ : ℝ)*neuronEnvelope n d := by
      simpa only [neuronEnvelope,mul_assoc] using hf
    linarith only [hc,he]
  exact conditional_width_bound hd hsize h₂ hfinite

#print axioms conditional_sqrt_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
