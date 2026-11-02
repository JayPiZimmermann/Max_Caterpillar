import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Laplace
import MaxCaterpillar.Frontier.RandomRestriction.CoinRankSizeBiasConstants

/-! # The actual weighted matching expression has constant four hundred

The factor multiplying the moment is displayed explicitly. This is not a
claim that an arbitrary sparse graph has moment at most 400/K^2.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
open BigOperators

private theorem rate_comparison (m K J t η : ℝ) (hm : 400≤m)
    (hK : 0<K) (hJ : K/2≤J) (ht : 0≤t) (hE : η-5*(m+4)≤t) :
    -(7/12 : ℝ)*J*t/(m*(m-1)) ≤ -(7/24 : ℝ)*K*(η-5*(m+4))/m^2 := by
  have hmpos : 0<m := by linarith only [hm]
  have hD : 0<m*(m-1) := mul_pos hmpos (by linarith only [hm])
  have hDle : m*(m-1)≤m^2 := by nlinarith only [hmpos.le]
  have hJnonneg : 0≤J := le_trans (by positivity : 0≤K/2) hJ
  have hfrac : (K/2)*(η-5*(m+4))/m^2 ≤ J*t/(m*(m-1)) := by
    calc
      _ ≤ (K/2)*t/m^2 := div_le_div_of_le_of_nonneg
        (mul_le_mul_of_nonneg_left hE (by positivity)) (sq_nonneg m)
      _ ≤ J*t/m^2 := div_le_div_of_le_of_nonneg
        (mul_le_mul_of_nonneg_right hJ ht) (sq_nonneg m)
      _ ≤ J*t/(m*(m-1)) :=
        div_le_div_of_le_left (mul_nonneg hJnonneg ht) hD hDle
  have hmul := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ)≤7/12)
  calc
    _ = -((7/12 : ℝ)*(J*t/(m*(m-1)))) := by ring
    _ ≤ -((7/12 : ℝ)*((K/2)*(η-5*(m+4))/m^2)) := neg_le_neg hmul
    _ = _ := by ring

/-- The verified four-hundred bound for the actual permutation matching
count, after multiplying by the stated local two-edge union-bound factor.
No exponential estimate or abstract coupling is assumed. -/
theorem actual_matching_counting_le_four_hundred {m J : ℕ}
    (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin J × Fin 2 → Fin m) (hP : Function.Injective P)
    (hG : 0<G.edgeFinset.card) (K η : ℝ)
    (hm : 400≤(m : ℝ)) (hK : 0<K) (hKcut : K≤(m : ℝ)/100)
    (hη : 0≤η) (hJ : K/2≤(J : ℝ))
    (hE : η-5*((m : ℝ)+4)≤(G.edgeFinset.card : ℝ)) :
    60*η^2/(m : ℝ)^4 *
        ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
          (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ))) ≤
      400/K^2 := by
  have hJpos : 0<J := by
    have hh : (0 : ℝ)<J := lt_of_lt_of_le (half_pos hK) hJ
    exact_mod_cast hh
  have hmoment := matching_half_moment_le G P hP hJpos hG
  have hrate := rate_comparison (m : ℝ) K (J : ℝ) (G.edgeFinset.card : ℝ) η
    hm hK hJ (Nat.cast_nonneg _) hE
  have hfactor : 0≤60*η^2/(m : ℝ)^4 := by positivity
  calc
    _ ≤ 60*η^2/(m : ℝ)^4 *
        Real.exp (-(7/12 : ℝ)*(J : ℝ)*(G.edgeFinset.card : ℝ)/
          ((m : ℝ)*((m : ℝ)-1))) := mul_le_mul_of_nonneg_left hmoment hfactor
    _ ≤ 60*η^2/(m : ℝ)^4 *
        Real.exp (-(7/24 : ℝ)*K*(η-5*((m : ℝ)+4))/(m : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) hfactor
    _ ≤ 400/K^2 := matching_counting_expression_le_four_hundred (m : ℝ) K η hm hK hKcut hη

#check @actual_matching_counting_le_four_hundred
#print axioms actual_matching_counting_le_four_hundred
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
