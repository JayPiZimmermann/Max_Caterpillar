import MaxCaterpillar.Frontier.RandomRestriction.MatchingAffine
import MaxCaterpillar.Frontier.RandomRestriction.CoinUniformityRank

/-! # Actual matching-fiber rank from proved flip differences

The finite state space is the actual permutation fiber. Its affine formula is
proved from one-step differences, then genuine single-bit equivalences supply
the conditional count. No uniform coin model is substituted for permutations.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Matching
open BigOperators
variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module ℝ V] {m : ℕ}

def fiberFlipSystem (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) :
    CoinFlipSystem (fun _ : Fiber slot u => ()) (fiberCoins slot u) :=
  ⟨fiberFlip slot u, fun _ _ => rfl, fiberCoins_flip slot u⟩

noncomputable def valueSolutions (slot : (ι × Bool) ↪ Fin m) (u : Data ι m)
    (F : Fiber slot u → V) (target : V) : Finset (Fiber slot u) := by
  classical
  exact Finset.univ.filter (fun p => F p = target)

/-- The rank bound for actual permutation states on one recorded-data fiber.
The vector difference hypothesis remains explicit until supplied by the actual
first-layer activation calculation. -/
theorem value_solution_card_mul (slot : (ι × Bool) ↪ Fin m) (u : Data ι m)
    (F : Fiber slot u → V) (columns : ι → V) (base : Fiber slot u)
    (hchange : ∀ i p, F (fiberFlip slot u i p) - F p =
      (coinCoefficient (!(fiberCoins slot u p i)) - coinCoefficient (fiberCoins slot u p i)) • columns i)
    (target : V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    (valueSolutions slot u F target).card * 2 ^ s.card ≤ Fintype.card (Fiber slot u) := by
  classical
  let offset := F base - ∑ j, coinCoefficient (fiberCoins slot u base j) • columns j
  have he : valueSolutions slot u F target =
      coinEventFiber (fun _ : Fiber slot u => ()) (fiberCoins slot u) ()
        (affineCoinSolutions offset target columns) := by
    ext p
    simp only [valueSolutions, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_coinEventFiber, eq_self_iff_true, mem_affineCoinSolutions]
    rw [affine_from_flip_differences slot u F columns base hchange p]
  rw [he]
  have hc := conditional_affine_coin_card_mul
    (fun _ : Fiber slot u => ()) (fiberCoins slot u) (fiberFlipSystem slot u) ()
    offset target columns s hindependent
  simpa [dataFiber] using hc

theorem value_solution_fraction_le (slot : (ι × Bool) ↪ Fin m) (u : Data ι m)
    (F : Fiber slot u → V) (columns : ι → V) (base : Fiber slot u)
    (hchange : ∀ i p, F (fiberFlip slot u i p) - F p =
      (coinCoefficient (!(fiberCoins slot u p i)) - coinCoefficient (fiberCoins slot u p i)) • columns i)
    (target : V) (s : Finset ι)
    (hindependent : LinearIndependent ℝ (fun i : s => columns i)) :
    ((valueSolutions slot u F target).card : ℝ) / Fintype.card (Fiber slot u) ≤
      1 / (2 : ℝ) ^ s.card := by
  have hc : ((valueSolutions slot u F target).card : ℝ) * (2 : ℝ) ^ s.card ≤
      Fintype.card (Fiber slot u) := by
    exact_mod_cast value_solution_card_mul slot u F columns base hchange target s hindependent
  have hpos : (0 : ℝ) < Fintype.card (Fiber slot u) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨base⟩
  apply (div_le_div_iff hpos (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  simpa only [one_mul] using hc

#print axioms value_solution_card_mul
#print axioms value_solution_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction.Matching
