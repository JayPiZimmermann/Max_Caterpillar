import MaxNN.Constructions.Paramid.Caterpillar.ConeBoundTransport
import MaxNN.Constructions.Paramid.Caterpillar.AllArities
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Global

/-! # Complete widths from the full caterpillar shape quotient

The bound includes all face corrections and the two signed remainder units.
-/

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

theorem essentialSecondWidth_le_spine (r : ℕ) (hr : 1 ≤ r) :
    essentialSecondWidth r ≤
      spineConeBound (r + 1 + 1) * 3 ^ r - (r + 1 + 1) * (r + 1) + 2 :=
  essentialSecondWidth_le_of_cone_bound r _ hr (card_normalizedWordCones_le_spine r)

theorem compactEssential_twoLayerWidth_spine (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1)
      ((r + 1 + 1).choose 2 + (r + 1 + 1) + 1)
      (spineConeBound (r + 1 + 1) * 3 ^ r - (r + 1 + 1) * (r + 1) + 2)
      (MAX (r + 1 + 1)) :=
  compactEssential_twoLayerWidth_of_cone_bound r _ hr
    (card_normalizedWordCones_le_spine r)

end MaxNN.Caterpillar

namespace MaxNN.Width

open Caterpillar.Corrections

/-- The closed full-shape bound for every positive input arity. -/
theorem MAX_twoLayerWidth_caterpillar_spine_all (N : ℕ) [NeZero N] :
    TwoLayerWidth N (N.choose 2 + N + 1)
      (spineConeBound N * 3 ^ (N - 2) - N * (N - 1) + 2) (MAX N) := by
  by_cases hN : 3 ≤ N
  · obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 + 1 := ⟨N - 2, by omega⟩
    rw [show r + 1 + 1 - 2 = r by omega, show r + 1 + 1 - 1 = r + 1 by omega]
    exact Caterpillar.compactEssential_twoLayerWidth_spine r (by omega)
  · have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hcases : N = 1 ∨ N = 2 := by omega
    rcases hcases with rfl | rfl
    · simpa using Caterpillar.compact_twoLayerWidth_MAX_one
    · simpa using Caterpillar.compact_twoLayerWidth_MAX_two

end MaxNN.Width
