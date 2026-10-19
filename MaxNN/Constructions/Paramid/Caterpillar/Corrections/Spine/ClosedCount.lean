import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Count

/-! # A finite closed count for caterpillar shapes

The summation index is the number of spine vertices minus two.  The four
factors choose the heads, order them up to reversal, choose the apex, and
attach all remaining leaves to heads.  The factorial is even in every term,
so the natural-number division loses no fractional contribution.
-/

namespace MaxNN.Caterpillar.Corrections

open scoped BigOperators

def spineConeTerm (N s : ℕ) : ℕ :=
  N.choose (s + 2) * ((s + 2).factorial / 2) * (N - (s + 2)) *
    (s + 2) ^ (N - (s + 3))

def spineConeBound (N : ℕ) : ℕ :=
  ∑ s in Finset.range (N - 2), spineConeTerm N s

theorem card_spineData_div_two (N s : ℕ) :
    Fintype.card (SpineData N s) / 2 = spineConeTerm N s := by
  have hf : 2 * ((s + 2).factorial / 2) = (s + 2).factorial :=
    Nat.mul_div_cancel' (Nat.dvd_factorial (by decide) (by omega))
  have hcard : Fintype.card (SpineData N s) = 2 * spineConeTerm N s := by
    rw [SpineData.card_spineData, spineConeTerm]
    calc
      _ = N.choose (s + 2) * (2 * ((s + 2).factorial / 2)) *
          (N - (s + 2)) * (s + 2) ^ (N - (s + 3)) := by rw [hf]
      _ = _ := by ring
  rw [hcard]
  simp

@[simp] theorem spineConeBound_one : spineConeBound 1 = 0 := by
  simp [spineConeBound]

@[simp] theorem spineConeBound_two : spineConeBound 2 = 0 := by
  simp [spineConeBound]

end MaxNN.Caterpillar.Corrections
