import MaxCaterpillar.Frontier.RandomRestriction.CoinUniformity
import MaxCaterpillar.Frontier.RandomRestriction.CoinRank

/-!
# Conditional affine-coin rank bound from genuine finite flip symmetries

This combines two verified finite ingredients: equal pattern-fiber sizes from
single-bit state-space equivalences, and the independent-column bound on the
number of Boolean solutions of an affine linear equation. Actual random-scale
configurations must still supply the equivalences and the affine survival map.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction

variable {ι Ω Data V : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
variable [AddCommGroup V] [Module ℝ V]

/-- A data fiber has at most a 2^(-r) fraction of affine solutions when r
selected columns are independent. This integer form includes empty fibers. -/
theorem conditional_affine_coin_card_mul
    (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data)
    (offset target : V) (columns : ι → V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    (coinEventFiber recorded coins d (affineCoinSolutions offset target columns)).card *
        2 ^ s.card ≤ (dataFiber recorded d).card := by
  let b : ι → Bool := fun _ => false
  rw [coin_event_card_eq recorded coins system d _ b,
    data_fiber_card_eq recorded coins system d b]
  have hc := affine_coin_solution_card_mul offset target columns s hindependent
  have hm := Nat.mul_le_mul_right (patternFiber recorded coins d b).card hc
  nlinarith only [hm]

/-- Conditional uniform finite counting on a nonempty data fiber. The flip
system is explicit, so fair and jointly independent coins are not assumed. -/
theorem conditional_affine_coin_fraction_le
    (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data)
    (hdata : 0 < (dataFiber recorded d).card)
    (offset target : V) (columns : ι → V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    ((coinEventFiber recorded coins d (affineCoinSolutions offset target columns)).card : ℝ) /
        (dataFiber recorded d).card ≤ 1 / (2 : ℝ) ^ s.card := by
  have hc :
      ((coinEventFiber recorded coins d (affineCoinSolutions offset target columns)).card : ℝ) *
        (2 : ℝ) ^ s.card ≤ (dataFiber recorded d).card := by
    exact_mod_cast conditional_affine_coin_card_mul recorded coins system d
      offset target columns s hindependent
  have hden : (0 : ℝ) < (dataFiber recorded d).card := by exact_mod_cast hdata
  apply (div_le_div_iff hden (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  simpa only [one_mul] using hc

#check @conditional_affine_coin_card_mul
#check @conditional_affine_coin_fraction_le
#print axioms conditional_affine_coin_card_mul
#print axioms conditional_affine_coin_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction
