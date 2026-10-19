import MaxNN.Constructions.Paramid.Caterpillar.Essential
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.HingeCount

/-! # Closed widths after absorbing all available pair hinges

The full normalized dictionary contains every ordered-pair hinge. Removing
these before counting saves at least `N * (N - 1)` dictionary entries. The
actual network also omits zero coefficients, so it obeys the same bound.
-/

namespace MaxNN.Caterpillar.Corrections

noncomputable local instance hingeBoundsRealKeyDecidableEq (n : ℕ) :
    DecidableEq (RealKey n) := Classical.decEq _

theorem essentialKeys_mono {n : ℕ} {K L : Finset (RealKey n)} (hKL : K ⊆ L) :
    essentialKeys K ⊆ essentialKeys L := by
  classical
  intro k hk
  obtain ⟨hkK, hkh⟩ := Finset.mem_sdiff.mp hk
  apply Finset.mem_sdiff.mpr
  refine ⟨hKL hkK, ?_⟩
  intro hkL
  exact hkh (Finset.mem_filter.mpr ⟨hkK, (Finset.mem_filter.mp hkL).2⟩)

end MaxNN.Caterpillar.Corrections

namespace MaxNN.Caterpillar

open Corrections MaxNN.Width

theorem essentialSecondWidth_le_normalized (r : ℕ) (hr : 1 ≤ r) :
    essentialSecondWidth r ≤
      (normalizedKeys r).card - (r + 1 + 1) * (r + 1) + 2 := by
  apply Nat.add_le_add_right
  apply (Finset.card_le_of_subset (essentialKeys_mono ?_)).trans
    (essentialNormalizedKeys_card_le_sub_orderedHinges hr)
  intro k hk
  exact (Finset.mem_filter.mp hk).1


end MaxNN.Caterpillar
