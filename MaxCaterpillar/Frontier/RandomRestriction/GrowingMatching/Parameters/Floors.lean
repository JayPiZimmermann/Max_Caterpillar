import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Actual integer braid parameters and floor bounds

The choices k=4q+1, m=n-k and K=m/100 are definitions. All size,
positivity, subtraction and floor estimates follow from one explicit
integer hypothesis; none is an envelope or probability assumption.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

def braidArity (q : ℕ) : ℕ := 4*q+1
def braidTail (n q : ℕ) : ℕ := n-braidArity q
def braidRanks (n q : ℕ) : ℕ := braidTail n q/100

/-- The exact finite bounds needed by the scalar and actual-network corollaries. -/
structure BraidParameterBounds (n q : ℕ) : Prop where
  total_lower : 160000 ≤ n
  arity_pos : 0 < braidArity q
  arity_lower : 3 ≤ braidArity q
  matching_arity : 2*q ≤ braidArity q
  arity_le_five_q : braidArity q ≤ 5*q
  twice_arity_le_total : 2*braidArity q ≤ n
  arity_le_half : braidArity q ≤ n/2
  arity_le_total : braidArity q ≤ n
  arity_le_tail : braidArity q ≤ braidTail n q
  total_eq : braidTail n q + braidArity q = n
  tail_lower : 80000 ≤ braidTail n q
  tail_four_hundred : 400 ≤ braidTail n q
  ranks_lower : 4 ≤ braidRanks n q
  ranks_lt_tail : braidRanks n q < braidTail n q
  ranks_upper : 100*braidRanks n q ≤ braidTail n q
  tail_le_two_hundred_ranks : braidTail n q ≤ 200*braidRanks n q
  ranks_lower_total : n ≤ 400*braidRanks n q
  total_add_two_le_three_tail : n+2 ≤ 3*braidTail n q
  shift_nat : n-1 ≤ 3*(braidTail n q-1)

/-- Every floor and positivity side condition follows from the stated integer size bound. -/
theorem braid_parameter_bounds (n q : ℕ) (hq : 1 ≤ q)
    (hsize : 160000*q^2 ≤ n) : BraidParameterBounds n q := by
  let k := braidArity q
  let m := braidTail n q
  let K := braidRanks n q
  have hq2 : q ≤ q^2 := by nlinarith only [hq]
  have hq21 : 1 ≤ q^2 := hq.trans hq2
  have hnlarge : 160000 ≤ n := by nlinarith only [hsize,hq21]
  have hlinear : 160000*q ≤ n := (Nat.mul_le_mul_left 160000 hq2).trans hsize
  have hk5 : k ≤ 5*q := by change 4*q+1 ≤ 5*q; linarith only [hq]
  have hkpos : 0 < k := by change 0 < 4*q+1; exact Nat.succ_pos _
  have hk3 : 3 ≤ k := by change 3 ≤ 4*q+1; linarith only [hq]
  have hmatch : 2*q ≤ k := by change 2*q ≤ 4*q+1; linarith
  have htwok : 2*k ≤ n := by
    change 2*(4*q+1) ≤ n
    linarith only [hlinear,hq]
  have hk_le : k ≤ n := by linarith only [htwok]
  have hk_half : k ≤ n/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    simpa only [Nat.mul_comm] using htwok
  have hsum : m+k = n := Nat.sub_add_cancel hk_le
  have hk_tail : k ≤ m := by linarith only [htwok,hsum]
  have hn2m : n ≤ 2*m := by linarith only [htwok,hsum]
  have hmlarge : 80000 ≤ m := by linarith only [hnlarge,hn2m]
  have hupper : 100*K ≤ m := by
    change 100*(m/100) ≤ m
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self m 100
  have hfloor : m < 100*(K+1) := Nat.lt_mul_div_succ m (by decide : 0 < 100)
  have hKfour : 4 ≤ K := by linarith only [hfloor,hmlarge]
  have hKlt : K < m := by linarith only [hupper,hmlarge]
  have hmlower : m ≤ 200*K := by linarith only [hfloor,hKfour]
  have hnlower : n ≤ 400*K := by linarith only [hn2m,hmlower]
  have hshift : n+2 ≤ 3*m := by linarith only [hn2m,hmlarge]
  have hnsub : n-1+1=n := Nat.sub_add_cancel (by linarith only [hnlarge])
  have hmsub : m-1+1=m := Nat.sub_add_cancel (by linarith only [hmlarge])
  have hshiftsub : n-1 ≤ 3*(m-1) := by linarith only [hshift,hnsub,hmsub]
  exact ⟨hnlarge,hkpos,hk3,hmatch,hk5,htwok,hk_half,hk_le,hk_tail,hsum,hmlarge,
    le_trans (by decide : 400 ≤ 80000) hmlarge,hKfour,hKlt,hupper,hmlower,hnlower,hshift,hshiftsub⟩

/-- Real half-size form, without natural-number division on the right. -/
theorem braidArity_le_half_real (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    (braidArity q : ℝ) ≤ (n : ℝ)/2 := by
  have h : 2*(braidArity q : ℝ) ≤ n := by
    exact_mod_cast (braid_parameter_bounds n q hq hsize).twice_arity_le_total
  linarith only [h]

/-- Real floor upper bound used in the exponential shift estimate. -/
theorem braidRanks_upper_real (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    100*(braidRanks n q : ℝ) ≤ (braidTail n q : ℝ) := by
  exact_mod_cast (braid_parameter_bounds n q hq hsize).ranks_upper

/-- Real floor lower bound used in the final base estimate. -/
theorem braidRanks_lower_real (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    (n : ℝ) ≤ 400*(braidRanks n q : ℝ) := by
  exact_mod_cast (braid_parameter_bounds n q hq hsize).ranks_lower_total

/-- The affine real shift comparison avoids natural subtraction truncation. -/
theorem braid_shift_real (n q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    (n : ℝ)-1 ≤ 3*((braidTail n q : ℝ)-1) := by
  have h : (n : ℝ)+2 ≤ 3*(braidTail n q : ℝ) := by
    exact_mod_cast (braid_parameter_bounds n q hq hsize).total_add_two_le_three_tail
  linarith only [h]

#check @braid_parameter_bounds
#print axioms braid_parameter_bounds
#print axioms braid_shift_real
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
