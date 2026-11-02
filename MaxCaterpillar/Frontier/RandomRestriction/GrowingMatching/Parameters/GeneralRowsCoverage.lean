import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.GeneralRows
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.SmallFalling

/-! # Positive coverage for the explicit integer general-row parameters

The internal-support and four-label contamination terms are bounded from their
literal descending factorials and the actual floor choice of rank count.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

private theorem arity_cube_budget (n d q : ℕ) (hq : 1≤q)
    (hcube : 1000*d^2*q^3≤n) : 8*d^2*(braidArity q)^3≤n := by
  have hk : braidArity q ≤ 5*q := by unfold braidArity; linarith only [hq]
  have hh := Nat.mul_le_mul_left (8*d^2) (Nat.pow_le_pow_left hk 3)
  nlinarith only [hh,hcube]

private theorem arity_square_budget (n d q : ℕ) (hd : 1≤d) (hq : 1≤q)
    (hcube : 1000*d^2*q^3≤n) : 40*d*(braidArity q)^2≤n := by
  have hk : braidArity q ≤ 5*q := by unfold braidArity; linarith only [hq]
  have hqq : q^2≤q^3 := by
    have hh := Nat.mul_le_mul_left (q^2) hq
    simpa only [mul_one,←pow_succ] using hh
  have hdd : d≤d^2 := by nlinarith only [hd]
  calc
    40*d*(braidArity q)^2 ≤ 40*d*(5*q)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 2)
    _ = 1000*d*q^2 := by ring
    _ ≤ 1000*d^2*q^3 := by
      have hh := Nat.mul_le_mul hdd hqq
      nlinarith only [hh]
    _ ≤ n := hcube

/-- Coverage at least one half, for arbitrary real row counts and moments satisfying the original quadratic budgets. No bad-event probability
estimate occurs as a hypothesis. -/
theorem general_row_coverage (n d q : ℕ) (hd : 1≤d) (hq : 1≤q)
    (hn : 8000*d^2≤n) (hcube : 1000*d^2*q^3≤n)
    (M L : ℝ)
    (hM : M≤(d : ℝ)^2*(n : ℝ)^2) (hL : L≤(d : ℝ)^2*(n : ℝ)^2) :
    (1/2 : ℝ) ≤ 1-8*(generalRanks n d q : ℝ)/(braidTail n q : ℝ)-
      M*( (braidArity q).descFactorial 3 : ℝ)/(n.descFactorial 3 : ℝ)-
      L/(n.descFactorial 4 : ℝ)*
        ((generalRanks n d q : ℝ)^2*(1+(braidArity q : ℝ)/(braidTail n q : ℝ))/
          (1-(generalRanks n d q : ℝ)/(braidTail n q : ℝ))+
          ((braidArity q).descFactorial 2 : ℝ)*(generalRanks n d q : ℝ)/2) := by
  let k := braidArity q
  let m := braidTail n q
  let K := generalRanks n d q
  have hb := general_row_parameter_bounds n d q hd hq hn hcube
  have hnR : (8000 : ℝ)≤n := by exact_mod_cast hb.total_lower
  have hn0 : (0 : ℝ)<n := by linarith only [hnR]
  have hmR : (400 : ℝ)≤m := by exact_mod_cast hb.tail_four_hundred
  have hm0 : (0 : ℝ)<m := by linarith only [hmR]
  have hK0 : (0 : ℝ)≤K := Nat.cast_nonneg K
  have hKm : 1000*(K : ℝ)≤m := by exact_mod_cast hb.ranks_upper_weak
  have hkM : (k : ℝ)≤m := by exact_mod_cast hb.arity_le_tail
  have hmn : m≤n := by linarith only [hb.total_eq]
  have hNK : 1000*(d : ℝ)*(K : ℝ)≤n := by
    exact_mod_cast hb.ranks_upper.trans hmn
  have hcubeR : 8*(d : ℝ)^2*(k : ℝ)^3≤n := by
    exact_mod_cast arity_cube_budget n d q hq hcube
  have hsquareR : 40*(d : ℝ)*(k : ℝ)^2≤n := by
    exact_mod_cast arity_square_budget n d q hd hq hcube
  have hD3 := descFactorial_three_lower n (by linarith only [hb.total_lower])
  have hD4 := descFactorial_four_lower n (by linarith only [hb.total_lower])
  have hk3 : ((k.descFactorial 3 : ℕ) : ℝ)≤(k : ℝ)^3 := by
    exact_mod_cast Nat.descFactorial_le_pow k 3
  have hk2 : ((k.descFactorial 2 : ℕ) : ℝ)≤(k : ℝ)^2 := by
    exact_mod_cast Nat.descFactorial_le_pow k 2
  have hB1 : M*(k.descFactorial 3 : ℝ)/(n.descFactorial 3 : ℝ)≤1/4 := by
    calc
      _ ≤ ((d : ℝ)^2*(n : ℝ)^2*(k : ℝ)^3)/((n : ℝ)^3/2) :=
        div_le_div (by positivity) (mul_le_mul hM hk3 (Nat.cast_nonneg _) (by positivity))
          (by positivity) hD3
      _ = 2*(d : ℝ)^2*(k : ℝ)^3/(n : ℝ) := by field_simp [hn0.ne']; ring
      _ ≤ 1/4 := (div_le_iff hn0).mpr (by nlinarith only [hcubeR])
  have hLR : L/(n.descFactorial 4 : ℝ)≤4*(d : ℝ)^2/(n : ℝ)^2 := by
    calc
      _ ≤ ((d : ℝ)^2*(n : ℝ)^2)/((n : ℝ)^4/4) :=
        div_le_div (by positivity) hL (by positivity) hD4
      _ = _ := by field_simp [hn0.ne']; ring
  have hQ : 8*(K : ℝ)/(m : ℝ)≤1/100 :=
    (div_le_iff hm0).mpr (by linarith only [hKm])
  have hKhalf : (K : ℝ)/(m : ℝ)≤1/2 :=
    (div_le_iff hm0).mpr (by linarith only [hKm])
  have hden : 0<1-(K : ℝ)/(m : ℝ) := by linarith only [hKhalf]
  have hkfrac : (k : ℝ)/(m : ℝ)≤1 := (div_le_iff hm0).mpr (by simpa using hkM)
  have hratio : (1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ))≤4 :=
    (div_le_iff hden).mpr (by linarith only [hKhalf,hkfrac])
  have hAnonneg : 0≤(K : ℝ)^2*((1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ))) := by positivity
  have hA : L/(n.descFactorial 4 : ℝ)*
      ((K : ℝ)^2*(1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ)))≤16/1000000 := by
    calc
      _ = L/(n.descFactorial 4 : ℝ)*((K : ℝ)^2*((1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ)))) := by ring
      _ ≤ (4*(d : ℝ)^2/(n : ℝ)^2)*((K : ℝ)^2*4) :=
        mul_le_mul hLR (mul_le_mul_of_nonneg_left hratio (sq_nonneg _)) hAnonneg (by positivity)
      _ = 16*(d : ℝ)^2*(K : ℝ)^2/(n : ℝ)^2 := by ring
      _ ≤ 16/1000000 := by
        apply (div_le_iff (pow_pos hn0 2)).mpr
        have hh := pow_le_pow_left (by positivity : (0 : ℝ)≤1000*(d : ℝ)*(K : ℝ)) hNK 2
        nlinarith only [hh]
  have hC : L/(n.descFactorial 4 : ℝ)*((k.descFactorial 2 : ℝ)*(K : ℝ)/2)≤1/20000 := by
    calc
      _ ≤ (4*(d : ℝ)^2/(n : ℝ)^2)*((k : ℝ)^2*(K : ℝ)/2) :=
        mul_le_mul hLR (div_le_div_of_le (by norm_num) (mul_le_mul_of_nonneg_right hk2 hK0)) (by positivity) (by positivity)
      _ = 2*(d : ℝ)^2*(k : ℝ)^2*(K : ℝ)/(n : ℝ)^2 := by ring
      _ ≤ 1/20000 := by
        apply (div_le_iff (pow_pos hn0 2)).mpr
        have hh := mul_le_mul hNK hsquareR (by positivity : (0 : ℝ)≤40*(d : ℝ)*(k : ℝ)^2) (by positivity : (0 : ℝ)≤n)
        nlinarith only [hh]
  have hB3 : L/(n.descFactorial 4 : ℝ)*
      ((K : ℝ)^2*(1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ))+
        (k.descFactorial 2 : ℝ)*(K : ℝ)/2)≤1/100 := by
    rw [mul_add]
    linarith only [hA,hC]
  change (1/2 : ℝ)≤1-8*(K : ℝ)/(m : ℝ)-M*(k.descFactorial 3 : ℝ)/(n.descFactorial 3 : ℝ)-_
  linarith only [hQ,hB1,hB3]

#print axioms general_row_coverage
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
