import MaxNN.Constructions.Paramid.Caterpillar.Construction
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Reversal
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.ReversalBounds
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.CompareBounds

/-! # A smaller closed second-layer bound from path reversal -/

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

/-- The full-cut path family contributes at most half of its permutations;
the other cut patterns retain the general word bound. -/
theorem secondWidth_le_reversal (r : ℕ) (hr : 1 ≤ r) :
    secondWidth r ≤
      ((r + 1 + 1).factorial * (2 ^ r - 2) + (r + 1 + 1).factorial / 2) *
        3 ^ r + 2 := by
  have hc := card_normalizedWordCones_le_reversal hr
  rw [card_wordIndex] at hc
  have he : (r + 1 + 1).factorial * (2 ^ r - 1) - (r + 1 + 1).factorial =
      (r + 1 + 1).factorial * (2 ^ r - 2) := by
    calc
      _ = (r + 1 + 1).factorial * ((2 ^ r - 1) - 1) := by
        simp only [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = _ := by rw [show (2 ^ r - 1) - 1 = 2 ^ r - 2 by omega]
  rw [he] at hc
  exact (secondWidth_le_normalizedCones r).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (3 ^ r) hc) 2)

theorem twoLayerWidth_reversal (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1) ((r + 1 + 1).choose 2 + 2 * (r + 1 + 1))
      (((r + 1 + 1).factorial * (2 ^ r - 2) + (r + 1 + 1).factorial / 2) *
        3 ^ r + 2) (MAX (r + 1 + 1)) := by
  rw [← firstWidth_eq]
  exact (twoLayerWidth r hr).mono_right (secondWidth_le_reversal r hr)

end MaxNN.Caterpillar

namespace MaxNN.Width

/-- A strict combinatorial reduction of the raw caterpillar word bound,
valid for every `N ≥ 3`. This bounds ordinary hidden ReLU layers. -/
theorem MAX_twoLayerWidth_caterpillar_reversal (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    TwoLayerWidth N (N.choose 2 + 2 * N)
      ((N.factorial * (2 ^ (N - 2) - 2) + N.factorial / 2) * 3 ^ (N - 2) + 2)
      (MAX N) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 + 1 := ⟨N - 2, by omega⟩
  rw [show r + 1 + 1 - 2 = r by omega]
  exact Caterpillar.twoLayerWidth_reversal r (by omega)

end MaxNN.Width
