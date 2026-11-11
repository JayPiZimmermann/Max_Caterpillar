import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Counting Boolean solutions from independent affine columns

This is the finite counting ingredient in fair-coin rank bounds. It makes
no assertion about Cartesian trees, conditional distributions, or networks.
The selected-column hypothesis is ordinary real linear independence.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module ℝ V]

def coinCoefficient (b : Bool) : ℝ := if b then 1 else 0

theorem coinCoefficient_injective : Function.Injective coinCoefficient := by
  intro a b hab
  cases a <;> cases b <;> norm_num [coinCoefficient] at hab ⊢

def affineCoinEval (offset : V) (columns : ι → V) (coins : ι → Bool) : V :=
  offset + ∑ i, coinCoefficient (coins i) • columns i

def outsideCoins (s : Finset ι) (coins : ι → Bool) : ↥(sᶜ) → Bool :=
  fun i => coins i

/-- Equal affine evaluations and equal unselected coins force equality of
all coins whenever the selected columns are linearly independent. -/
theorem affine_coin_fiber_projection_injective
    (offset target : V) (columns : ι → V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    Set.InjOn (outsideCoins s) {coins | affineCoinEval offset columns coins = target} := by
  classical
  intro a ha b hb hab
  have houtside : ∀ i ∉ s, a i = b i := by
    intro i hi
    exact congrFun hab ⟨i, Finset.mem_compl.mpr hi⟩
  have hwhole :
      (∑ i, (coinCoefficient (a i) - coinCoefficient (b i)) • columns i) = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    exact add_left_cancel (ha.trans hb.symm)
  have hselected :
      (∑ i in s, (coinCoefficient (a i) - coinCoefficient (b i)) • columns i) = 0 := by
    calc
      _ = ∑ i, (coinCoefficient (a i) - coinCoefficient (b i)) • columns i := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        rw [houtside i hi, sub_self, zero_smul]
      _ = 0 := hwhole
  have hsubtype :
      (∑ i : s, (coinCoefficient (a i) - coinCoefficient (b i)) • columns i) = 0 := by
    rw [Finset.sum_coe_sort s
      (fun i => (coinCoefficient (a i) - coinCoefficient (b i)) • columns i)]
    exact hselected
  have hzero := Fintype.linearIndependent_iff.mp hindependent
    (fun i : s => coinCoefficient (a i) - coinCoefficient (b i)) hsubtype
  funext i
  by_cases hi : i ∈ s
  · exact coinCoefficient_injective (sub_eq_zero.mp (hzero ⟨i, hi⟩))
  · exact houtside i hi

noncomputable def affineCoinSolutions (offset target : V) (columns : ι → V) :
    Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter (fun coins => affineCoinEval offset columns coins = target)

@[simp] theorem mem_affineCoinSolutions (offset target : V) (columns : ι → V)
    (coins : ι → Bool) :
    coins ∈ affineCoinSolutions offset target columns ↔
      affineCoinEval offset columns coins = target := by
  classical
  simp only [affineCoinSolutions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- At most 2^(n-r) Boolean solutions, with n the number of columns and r
the number of selected independent columns. -/
theorem affine_coin_solution_card_le
    (offset target : V) (columns : ι → V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    (affineCoinSolutions offset target columns).card ≤
      2 ^ (Fintype.card ι - s.card) := by
  classical
  have hinj : Set.InjOn (outsideCoins s) (affineCoinSolutions offset target columns) := by
    intro a ha b hb hab
    exact affine_coin_fiber_projection_injective offset target columns s hindependent
      (mem_affineCoinSolutions offset target columns a |>.mp ha)
      (mem_affineCoinSolutions offset target columns b |>.mp hb) hab
  calc
    _ = ((affineCoinSolutions offset target columns).image (outsideCoins s)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card (↥(sᶜ) → Bool) := Finset.card_le_univ _
    _ = 2 ^ (Fintype.card ι - s.card) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl]

/-- Integer multiplication form of the fair-coin rank estimate. -/
theorem affine_coin_solution_card_mul
    (offset target : V) (columns : ι → V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    (affineCoinSolutions offset target columns).card * 2 ^ s.card ≤
      2 ^ Fintype.card ι := by
  calc
    _ ≤ 2 ^ (Fintype.card ι - s.card) * 2 ^ s.card :=
      Nat.mul_le_mul_right _ (affine_coin_solution_card_le offset target columns s hindependent)
    _ = 2 ^ Fintype.card ι := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_univ s)]

/-- The uniform finite fraction is at most 2^(-r). This theorem uses only
finite counting, and supplies no conditional independence assumption. -/
theorem affine_coin_uniform_fraction_le
    (offset target : V) (columns : ι → V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    ((affineCoinSolutions offset target columns).card : ℝ) /
        (2 : ℝ) ^ Fintype.card ι ≤ 1 / (2 : ℝ) ^ s.card := by
  have hc : ((affineCoinSolutions offset target columns).card : ℝ) *
      (2 : ℝ) ^ s.card ≤ (2 : ℝ) ^ Fintype.card ι := by
    exact_mod_cast affine_coin_solution_card_mul offset target columns s hindependent
  apply (div_le_div_iff (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  simpa only [one_mul] using hc

end MaxCaterpillar.Frontier.RandomRestriction
