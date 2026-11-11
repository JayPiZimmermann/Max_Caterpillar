import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Exact Bernoulli parameter side conditions

All estimates concern the literal definitions in Defs. They follow from
integer d>=1 and n>=10^10 d^2. No probability or envelope estimate is assumed.
Only symbolic square-root and floor inequalities are used.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

/-- The literal integer quotient agrees with its real-floor presentation. -/
theorem rankCount_eq_floor (n d : ℕ) :
    rankCount n d = Nat.floor ((n : ℝ)/(1000*(d : ℝ)^2)) := by
  have h := Nat.floor_div_nat (n : ℝ) (1000*d^2)
  rw [Nat.floor_coe] at h
  simpa only [rankCount,Nat.cast_mul,Nat.cast_pow] using h.symm

/-- Exact second-moment identity, including the zero-input boundary. -/
theorem mean_sq (n d : ℕ) :
    (bernoulliMean n d)^2 = (alpha d)^2 * (n : ℝ) := by
  simp only [bernoulliMean,alpha,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

private lemma inverse_product_mul_square (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (1/(a*b))*(b*b) = b/a := by
  field_simp [ha,hb] <;> ring

/-- Exact normalization of the one-label selection probability. -/
theorem probability_mul_total (n d : ℕ) (hn : 0 < n) (hd : 1 ≤ d) :
    selectionProbability n d * (n : ℝ) = bernoulliMean n d := by
  let s := Real.sqrt (n : ℝ)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hd
  have hspos : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq : s*s = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
  change (1/(1000*(d : ℝ)*s))*(n : ℝ) = s/(1000*(d : ℝ))
  calc
    (1/(1000*(d : ℝ)*s))*(n : ℝ) = (1/(1000*(d : ℝ)*s))*(s*s) :=
      congrArg (fun x : ℝ => (1/(1000*(d : ℝ)*s))*x) hsq.symm
    _ = s/(1000*(d : ℝ)) := inverse_product_mul_square _ _
      (mul_ne_zero (by norm_num : (1000 : ℝ) ≠ 0) hdpos.ne') hspos.ne'

/-- The key exact p^2 n = alpha^2 relation used by the support budget. -/
theorem probability_sq_mul_total (n d : ℕ) (hn : 0 < n) (hd : 1 ≤ d) :
    (selectionProbability n d)^2 * (n : ℝ) = (alpha d)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply mul_right_cancel₀ hnR.ne'
  calc
    ((selectionProbability n d)^2*(n : ℝ))*(n : ℝ) =
        (selectionProbability n d*(n : ℝ))^2 := by ring
    _ = (bernoulliMean n d)^2 := congrArg (fun x : ℝ => x^2) (probability_mul_total n d hn hd)
    _ = (alpha d)^2*(n : ℝ) := mean_sq n d

/-- Explicit square of alpha, with its full d dependence. -/
theorem alpha_sq (d : ℕ) : (alpha d)^2 = 1/(1000000*(d : ℝ)^2) := by
  simp only [alpha,div_pow,one_pow,mul_pow]
  norm_num

structure ParameterBounds (n d : ℕ) : Prop where
  n_pos : 0 < n
  d_pos : 0 < d
  sqrt_pos : 0 < Real.sqrt (n : ℝ)
  mean_lower : 100 ≤ bernoulliMean n d
  probability_pos : 0 < selectionProbability n d
  probability_le_thousandth : selectionProbability n d ≤ 1/1000
  probability_le_one : selectionProbability n d ≤ 1
  order_pos : 1 ≤ matchingOrder n d
  order_lower : bernoulliMean n d/9 ≤ (matchingOrder n d : ℝ)
  order_upper : (matchingOrder n d : ℝ) ≤ bernoulliMean n d/8
  arity_upper : (minimumArity n d : ℝ) ≤ 3*bernoulliMean n d/5
  cap_upper : (selectedCap n d : ℝ) ≤ 2*bernoulliMean n d
  cap_le_total : selectedCap n d ≤ n
  tail_add_cap : minimumTail n d + selectedCap n d = n
  total_le_twice_tail : n ≤ 2*minimumTail n d
  tail_lower400 : 400 ≤ minimumTail n d
  ranks_lower : 4 ≤ rankCount n d
  hundred_ranks_le_tail : 100*rankCount n d ≤ minimumTail n d
  ranks_real_lower : delta d*(n : ℝ)/2 ≤ (rankCount n d : ℝ)
  ranks_real_upper : (rankCount n d : ℝ) ≤ delta d*(n : ℝ)
  delta_pos : 0 < delta d
  delta_upper : delta d ≤ 1/1000
  arity_le_cap : minimumArity n d ≤ selectedCap n d

/-- All floor, positivity and size hypotheses required by the Bernoulli scalar route. -/
theorem parameter_bounds (n d : ℕ) (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    ParameterBounds n d := by
  let D : ℝ := d
  let N : ℝ := n
  let s := Real.sqrt N
  let μ := bernoulliMean n d
  let K := rankCount n d
  have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 1) hd
  have hD1 : (1 : ℝ) ≤ D := by change (1 : ℝ) ≤ (d : ℝ); exact_mod_cast hd
  have hDpos : 0 < D := by change (0 : ℝ) < (d : ℝ); exact_mod_cast hdpos
  have hDsq : (1 : ℝ) ≤ D^2 := by nlinarith only [hD1]
  have hdSqNat : 1 ≤ d^2 := by nlinarith only [hd]
  have hnlarge : 10000000000 ≤ n := by nlinarith only [hn,hdSqNat]
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 10000000000) hnlarge
  have hNpos : 0 < N := by change (0 : ℝ) < (n : ℝ); exact_mod_cast hnpos
  have hNnn : 0 ≤ N := hNpos.le
  have hsize : (10000000000 : ℝ)*D^2 ≤ N := by
    change (10000000000 : ℝ)*(d : ℝ)^2 ≤ (n : ℝ)
    exact_mod_cast hn
  have hsnn : 0 ≤ s := Real.sqrt_nonneg N
  have hspos : 0 < s := Real.sqrt_pos.mpr hNpos
  have hssq : s^2 = N := Real.sq_sqrt hNnn
  have hsLower : 100000*D ≤ s := by
    apply (Real.le_sqrt (by positivity) hNnn).mpr
    nlinarith only [hsize]
  have hs1 : 1 ≤ s := by linarith only [hsLower,hD1]
  have hsN : s ≤ N := by
    calc
      s ≤ s*s := le_mul_of_one_le_right hsnn hs1
      _ = N := by nlinarith only [hssq]
  have hden : 0 < 1000*D := mul_pos (by norm_num) hDpos
  have hdenSq : 0 < 1000*D^2 := mul_pos (by norm_num) (sq_pos_of_pos hDpos)
  have hμdef : μ = s/(1000*D) := rfl
  have hμ100 : 100 ≤ μ := by
    rw [hμdef]
    apply (le_div_iff hden).mpr
    linarith only [hsLower]
  have hμnn : 0 ≤ μ := le_trans (by norm_num) hμ100
  have hND : N ≤ N*D := le_mul_of_one_le_right hNnn hD1
  have hμupper : μ ≤ N/1000 := by
    rw [hμdef]
    apply (div_le_div_iff hden (by norm_num : (0 : ℝ) < 1000)).mpr
    nlinarith only [hsN,hND]
  have hDS : 1 ≤ D*s := by
    calc
      (1 : ℝ) = 1*1 := by ring
      _ ≤ D*s := mul_le_mul hD1 hs1 (by norm_num) hDpos.le
  have hPden : 0 < 1000*D*s := mul_pos hden hspos
  have hpPos : 0 < selectionProbability n d := by
    change 0 < 1/(1000*D*s)
    exact div_pos (by norm_num) hPden
  have hpUpper : selectionProbability n d ≤ 1/1000 := by
    change 1/(1000*D*s) ≤ 1/1000
    apply (div_le_iff hPden).mpr
    nlinarith only [hDS]
  have hdeltaPos : 0 < delta d := div_pos (by norm_num) hdenSq
  have hdeltaUpper : delta d ≤ 1/1000 := by
    change 1/(1000*D^2) ≤ 1/1000
    apply (div_le_iff hdenSq).mpr
    nlinarith only [hDsq]
  have hqUpper : (matchingOrder n d : ℝ) ≤ μ/8 :=
    Nat.floor_le (div_nonneg hμnn (by norm_num))
  have hqFloor : μ/8 < (matchingOrder n d : ℝ)+1 := Nat.lt_floor_add_one (μ/8)
  have hqLower : μ/9 ≤ (matchingOrder n d : ℝ) := by linarith only [hqFloor,hμ100]
  have hqPosR : (1 : ℝ) ≤ (matchingOrder n d : ℝ) := by linarith only [hqLower,hμ100]
  have hqPos : 1 ≤ matchingOrder n d := by exact_mod_cast hqPosR
  have hArity : (minimumArity n d : ℝ) = 4*(matchingOrder n d : ℝ)+1 := by
    simp only [minimumArity,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    rfl
  have hArityUpper : (minimumArity n d : ℝ) ≤ 3*μ/5 := by rw [hArity]; linarith only [hqUpper,hμ100]
  have hCapUpper : (selectedCap n d : ℝ) ≤ 2*μ := Nat.floor_le (mul_nonneg (by norm_num) hμnn)
  have hCapFloor : 2*μ < (selectedCap n d : ℝ)+1 := Nat.lt_floor_add_one (2*μ)
  have hCapHalf : (selectedCap n d : ℝ) ≤ N/2 := by linarith only [hCapUpper,hμupper,hNnn]
  have hCapTotalR : (selectedCap n d : ℝ) ≤ N := by linarith only [hCapHalf,hNnn]
  have hCapTotal : selectedCap n d ≤ n := by
    have h := hCapTotalR
    dsimp only [N] at h
    exact_mod_cast h
  have hsum : minimumTail n d + selectedCap n d = n := Nat.sub_add_cancel hCapTotal
  have hsumR : (minimumTail n d : ℝ)+(selectedCap n d : ℝ)=N := by
    change (minimumTail n d : ℝ)+(selectedCap n d : ℝ)=(n : ℝ)
    exact_mod_cast hsum
  have hHalfTail : N/2 ≤ (minimumTail n d : ℝ) := by linarith only [hsumR,hCapHalf]
  have hNtwomR : N ≤ 2*(minimumTail n d : ℝ) := by linarith only [hHalfTail]
  have hNtwom : n ≤ 2*minimumTail n d := by
    have h := hNtwomR
    dsimp only [N] at h
    exact_mod_cast h
  have hm400 : 400 ≤ minimumTail n d := by linarith only [hnlarge,hNtwom]
  have hZdef : delta d*N = N/(1000*D^2) := by unfold delta; ring
  have hZlarge : 10000000 ≤ delta d*N := by
    rw [hZdef]
    apply (le_div_iff hdenSq).mpr
    nlinarith only [hsize]
  have hKfloor : delta d*N < (K : ℝ)+1 := by
    change delta d*N < (rankCount n d : ℝ)+1
    rw [rankCount_eq_floor]
    rw [hZdef]
    exact Nat.lt_floor_add_one _
  have hKupper : (K : ℝ) ≤ delta d*N := by
    change (rankCount n d : ℝ) ≤ delta d*N
    rw [rankCount_eq_floor,hZdef]
    exact Nat.floor_le (div_nonneg hNnn hdenSq.le)
  have hKlower : delta d*N/2 ≤ (K : ℝ) := by linarith only [hKfloor,hZlarge]
  have hKfourR : (4 : ℝ) ≤ (K : ℝ) := by linarith only [hKfloor,hZlarge]
  have hKfour : 4 ≤ K := by exact_mod_cast hKfourR
  have hδN := mul_le_mul_of_nonneg_right hdeltaUpper hNnn
  have hKweak : (K : ℝ) ≤ (1/1000)*N := hKupper.trans hδN
  have hhundredR : 100*(K : ℝ) ≤ (minimumTail n d : ℝ) := by linarith only [hKweak,hHalfTail,hNnn]
  have hhundred : 100*K ≤ minimumTail n d := by exact_mod_cast hhundredR
  have hArityCapR : (minimumArity n d : ℝ) ≤ (selectedCap n d : ℝ) := by
    linarith only [hArityUpper,hCapFloor,hμ100]
  have hArityCap : minimumArity n d ≤ selectedCap n d := by exact_mod_cast hArityCapR
  exact ⟨hnpos,hdpos,hspos,hμ100,hpPos,hpUpper,le_trans hpUpper (by norm_num),hqPos,
    hqLower,hqUpper,hArityUpper,hCapUpper,hCapTotal,hsum,hNtwom,hm400,hKfour,
    hhundred,hKlower,hKupper,hdeltaPos,hdeltaUpper,hArityCap⟩

#check @parameter_bounds
#check @probability_sq_mul_total
#print axioms parameter_bounds
#print axioms probability_sq_mul_total
#print axioms rankCount_eq_floor
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
