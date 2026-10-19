import MaxNN.Constructions.Paramid.Caterpillar.Corrections.NormalizeFaces
import Mathlib.Data.Fintype.Perm

/-! # Closed cardinal bounds for the finite caterpillar dictionary -/

namespace MaxNN.Caterpillar.Corrections

open MaxNN.Width

variable {r : ℕ}

theorem card_admissibleCuts (r : ℕ) : (admissibleCuts r).card = 2 ^ r - 1 := by
  unfold admissibleCuts
  rw [Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.empty_subset _)),
    Finset.card_powerset]
  unfold cutPositions
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]

theorem card_wordIndex (r : ℕ) :
    Fintype.card (WordIndex r) = (r + 1 + 1).factorial * (2 ^ r - 1) := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_coe,
    card_admissibleCuts]

theorem card_normalizedWordCones_le_factorial :
    (normalizedWordCones r).card ≤ (r + 1 + 1).factorial * (2 ^ r - 1) := by
  have h := card_normalizedWordCones_le.trans (card_wordCones_le (r := r))
  rwa [card_wordIndex] at h

theorem CorrectionTable.card_normalizedActiveKeys_le_factorial (T : CorrectionTable r) :
    T.normalizedActiveKeys.card ≤ (r + 1 + 1).factorial * (2 ^ r - 1) * 3 ^ r := by
  exact T.card_normalizedActiveKeys_le.trans
    (card_normalizedKeys_le_normalizedWordCones.trans
      (Nat.mul_le_mul_right (3 ^ r) card_normalizedWordCones_le_factorial))

/-- A closed bound in the input dimension; the actual network has the
smaller normalized, merged, nonzero coefficient support. -/
theorem twoLayerWidth_MAX_factorial_bound (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1))
      ((r + 1 + 1).factorial * (2 ^ r - 1) * 3 ^ r + 2) (MAX (r + 1 + 1)) := by
  apply (twoLayerWidth_MAX_normalizedCone_bound hr hclass).mono_right
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right (3 ^ r) card_normalizedWordCones_le_factorial) 2

end MaxNN.Caterpillar.Corrections
