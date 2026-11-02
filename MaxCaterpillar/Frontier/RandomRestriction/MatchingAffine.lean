import MaxCaterpillar.Frontier.RandomRestriction.MatchingFiber
import MaxCaterpillar.Frontier.RandomRestriction.CoinRank

/-!
# Integrate proved matching-flip differences into an affine coin formula

The hypothesis is an actual one-step vector difference for every matching
transposition. The affine formula is derived using the genuine permutation
fiber and its proved coin separation; it is not assumed as a network model.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Matching
open BigOperators

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module ℝ V] {m : ℕ}

lemma coin_sum_flip (columns : ι → V) (i : ι) (b : ι → Bool) :
    (∑ j, coinCoefficient (flipBit i b j) • columns j) =
      (∑ j, coinCoefficient (b j) • columns j) +
        (coinCoefficient (!(b i)) - coinCoefficient (b i)) • columns i := by
  classical
  calc
    _ = ∑ j, (coinCoefficient (b j) • columns j +
        if j = i then (coinCoefficient (!(b i)) - coinCoefficient (b i)) • columns i else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp only [flipBit, eq_self_iff_true, ite_true]
        rw [sub_smul]
        abel
      · simp only [flipBit, if_neg hj, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- An actual flip-difference identity determines the affine readout on an
entire local-data fiber, with an explicit offset at any chosen base state. -/
theorem affine_from_flip_differences (slot : (ι × Bool) ↪ Fin m) (u : Data ι m)
    (F : Fiber slot u → V) (columns : ι → V) (base : Fiber slot u)
    (hchange : ∀ i p, F (fiberFlip slot u i p) - F p =
      (coinCoefficient (!(fiberCoins slot u p i)) - coinCoefficient (fiberCoins slot u p i)) • columns i)
    (p : Fiber slot u) :
    F p = affineCoinEval
      (F base - ∑ j, coinCoefficient (fiberCoins slot u base j) • columns j)
      columns (fiberCoins slot u p) := by
  let H : Fiber slot u → V := fun p => F p - ∑ j, coinCoefficient (fiberCoins slot u p j) • columns j
  have hH : ∀ i p, H (fiberFlip slot u i p) = H p := by
    intro i p
    have hF := sub_eq_iff_eq_add.mp (hchange i p)
    have hsum : (∑ j, coinCoefficient (fiberCoins slot u (fiberFlip slot u i p) j) • columns j) =
        (∑ j, coinCoefficient (fiberCoins slot u p j) • columns j) +
          (coinCoefficient (!(fiberCoins slot u p i)) - coinCoefficient (fiberCoins slot u p i)) • columns i := by
      rw [fiberCoins_flip]
      exact coin_sum_flip columns i (fiberCoins slot u p)
    dsimp only [H]
    rw [hF, hsum]
    abel
  have he := invariant_constant slot u H hH p base
  dsimp only [H] at he
  unfold affineCoinEval
  exact sub_eq_iff_eq_add.mp he

#check @affine_from_flip_differences
#print axioms coin_sum_flip
#print axioms affine_from_flip_differences
end MaxCaterpillar.Frontier.RandomRestriction.Matching
