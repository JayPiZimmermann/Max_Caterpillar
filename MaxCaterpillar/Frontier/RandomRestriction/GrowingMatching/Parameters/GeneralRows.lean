import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Floors
import Mathlib.Tactic

/-! # Integer parameters for the general-row conditional corollary

All side conditions follow from explicit integer size and cubic-budget bounds.
The selected arity and tail use the same definitions as the braid parameters;
the rank denominator is 1000*d, with integer d at least one.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

def generalRanks (n d q : ℕ) : ℕ := braidTail n q / (1000*d)

structure GeneralRowParameterBounds (n d q : ℕ) : Prop where
  total_lower : 8000 ≤ n
  d_pos : 0 < d
  q_pos : 0 < q
  arity_pos : 0 < braidArity q
  arity_lower : 3 ≤ braidArity q
  matching_arity : 2*q ≤ braidArity q
  arity_le_five_q : braidArity q ≤ 5*q
  twice_arity_le_total : 2*braidArity q ≤ n
  arity_le_total : braidArity q ≤ n
  arity_le_tail : braidArity q ≤ braidTail n q
  total_eq : braidTail n q + braidArity q = n
  tail_lower : 4000*d^2 ≤ braidTail n q
  tail_four_hundred : 400 ≤ braidTail n q
  ranks_lower : 4 ≤ generalRanks n d q
  ranks_lt_tail : generalRanks n d q < braidTail n q
  ranks_upper : 1000*d*generalRanks n d q ≤ braidTail n q
  ranks_upper_weak : 1000*generalRanks n d q ≤ braidTail n q
  ranks_lower_total : n ≤ 4000*d*generalRanks n d q
  total_add_two_le_three_tail : n+2 ≤ 3*braidTail n q

 theorem general_row_parameter_bounds (n d q : ℕ) (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hn : 8000*d^2 ≤ n) (hcube : 1000*d^2*q^3 ≤ n) :
    GeneralRowParameterBounds n d q := by
  let k := braidArity q
  let m := braidTail n q
  let K := generalRanks n d q
  have hd2 : 1 ≤ d^2 := by nlinarith only [hd]
  have hdd2 : d ≤ d^2 := by nlinarith only [hd]
  have hq2 : q ≤ q^2 := by nlinarith only [hq]
  have hq23 : q^2 ≤ q^3 := by
    have hh := Nat.mul_le_mul_left (q^2) hq
    simpa only [mul_one, ←pow_succ] using hh
  have hq3 : q ≤ q^3 := hq2.trans hq23
  have hlinear : 1000*q ≤ n := by
    have hh := Nat.mul_le_mul_right (q^3) hd2
    nlinarith only [hh,hq3,hcube]
  have hnlarge : 8000 ≤ n := by nlinarith only [hn,hd2]
  have hk5 : k ≤ 5*q := by change 4*q+1 ≤ 5*q; linarith only [hq]
  have hkpos : 0 < k := by change 0 < 4*q+1; exact Nat.succ_pos _
  have hk3 : 3 ≤ k := by change 3 ≤ 4*q+1; linarith only [hq]
  have hmatch : 2*q ≤ k := by change 2*q ≤ 4*q+1; linarith
  have htwok : 2*k ≤ n := by
    change 2*(4*q+1) ≤ n
    linarith only [hlinear,hq]
  have hk_le : k ≤ n := by linarith only [htwok]
  have hsum : m+k = n := Nat.sub_add_cancel hk_le
  have hk_tail : k ≤ m := by linarith only [htwok,hsum]
  have hn2m : n ≤ 2*m := by linarith only [htwok,hsum]
  have hmlarge : 4000*d^2 ≤ m := by linarith only [hn,hn2m]
  have hm400 : 400 ≤ m := by nlinarith only [hmlarge,hd2]
  have hmd : 4000*d ≤ m := by nlinarith only [hmlarge,hdd2]
  have hden : 0 < 1000*d := Nat.mul_pos (by decide) (lt_of_lt_of_le (by decide : 0<1) hd)
  have hupper : 1000*d*K ≤ m := by
    change 1000*d*(m/(1000*d)) ≤ m
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self m (1000*d)
  have hKfour : 4 ≤ K := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    nlinarith only [hmd]
  have hfloor : m < (1000*d)*(K+1) := Nat.lt_mul_div_succ m hden
  have hupperweak : 1000*K ≤ m := by
    have hh := Nat.mul_le_mul_left (1000*K) hd
    nlinarith only [hh,hupper]
  have hKlt : K < m := by linarith only [hupperweak,hm400]
  have hmlower : m ≤ 2000*d*K := by
    have hh := Nat.mul_le_mul_left d (show 1≤K by linarith only [hKfour])
    nlinarith only [hh,hfloor]
  have hnlower : n ≤ 4000*d*K := by linarith only [hn2m,hmlower]
  have hshape : n+2 ≤ 3*m := by linarith only [hn2m,hm400]
  exact ⟨hnlarge,lt_of_lt_of_le (by decide : 0<1) hd,lt_of_lt_of_le (by decide : 0<1) hq,
    hkpos,hk3,hmatch,hk5,htwok,hk_le,hk_tail,hsum,hmlarge,hm400,hKfour,hKlt,
    hupper,hupperweak,hnlower,hshape⟩

#print axioms general_row_parameter_bounds
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
