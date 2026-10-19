import MaxNN.Constructions.Paramid.Caterpillar.HingeBounds

/-! # Transporting cone counts to complete network widths

A cone count includes neither face corrections nor the signed pair-linear
remainder.  These lemmas account for both, and absorb all ordered-pair hinges
before bounding the complete second hidden layer.
-/

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

theorem essentialSecondWidth_le_of_cone_bound (r b : ℕ) (hr : 1 ≤ r)
    (hb : (normalizedWordCones r).card ≤ b) :
    essentialSecondWidth r ≤ b * 3 ^ r - (r + 1 + 1) * (r + 1) + 2 := by
  have hk : (normalizedKeys r).card ≤ b * 3 ^ r :=
    card_normalizedKeys_le_normalizedWordCones.trans
      (Nat.mul_le_mul_right _ hb)
  exact (essentialSecondWidth_le_normalized r hr).trans
    (Nat.add_le_add_right (Nat.sub_le_sub_right hk _) 2)

theorem compactEssential_twoLayerWidth_of_cone_bound (r b : ℕ) (hr : 1 ≤ r)
    (hb : (normalizedWordCones r).card ≤ b) :
    TwoLayerWidth (r + 1 + 1)
      ((r + 1 + 1).choose 2 + (r + 1 + 1) + 1)
      (b * 3 ^ r - (r + 1 + 1) * (r + 1) + 2) (MAX (r + 1 + 1)) :=
  (compactEssential_twoLayerWidth r hr).mono_right
    (essentialSecondWidth_le_of_cone_bound r b hr hb)

end MaxNN.Caterpillar
