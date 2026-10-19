import MaxNN.Constructions.Paramid.Caterpillar.Words.Translation
import Mathlib.GroupTheory.Perm.Basic

/-! # The explicit decorated-word candidate

This finite formula is a candidate for the top-dimensional simplex identity.
Its definition has no smaller-arity calls. The results here prove symmetry and
translation of the actual sum, not that the candidate equals MAX or differs
from MAX by a lower-dimensional support function.

The translation coefficient is kept explicit: it must not be assumed to be
one. Lower-dimensional corrections can include linear terms.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ}

def admissibleCuts (r : ℕ) : Finset (Finset (Fin (r + 1))) :=
  (cutPositions r).powerset.erase ∅

noncomputable def wordWeight (r : ℕ) (S : Finset (Fin (r + 1))) : ℝ :=
  (Nat.factorial (r + 1 + 1) : ℝ)⁻¹ * (-1 : ℝ) ^ (r + 1 + 1 + S.card)

noncomputable def valueUnit (x : Fin (r + 1 + 1) → ℝ)
    (π : Equiv.Perm (Fin (r + 1 + 1))) (S : Finset (Fin (r + 1))) : ℝ :=
  max (x (π 0)) (baseMax (fun i : Fin (r + 1) => x (π i.succ)) S)

noncomputable def valueFormula (r : ℕ) (x : Fin (r + 1 + 1) → ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin (r + 1 + 1)),
    ∑ S in admissibleCuts r, wordWeight r S * valueUnit x π S

noncomputable def totalWeight (r : ℕ) : ℝ :=
  ∑ _π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r, wordWeight r S

theorem valueUnit_add_const (x : Fin (r + 1 + 1) → ℝ) (c : ℝ)
    (π : Equiv.Perm (Fin (r + 1 + 1))) (S : Finset (Fin (r + 1))) :
    valueUnit (fun i => x i + c) π S = valueUnit x π S + c := by
  unfold valueUnit
  rw [baseMax_add_const]
  exact max_add_add_right _ _ _

theorem valueFormula_add_const (x : Fin (r + 1 + 1) → ℝ) (c : ℝ) :
    valueFormula r (fun i => x i + c) = valueFormula r x + totalWeight r * c := by
  unfold valueFormula totalWeight
  simp only [valueUnit_add_const, mul_add, Finset.sum_add_distrib, Finset.sum_mul]

theorem valueFormula_permute (x : Fin (r + 1 + 1) → ℝ)
    (τ : Equiv.Perm (Fin (r + 1 + 1))) : valueFormula r (fun i => x (τ i)) = valueFormula r x := by
  unfold valueFormula
  apply Fintype.sum_equiv (Equiv.mulLeft τ)
  intro π
  rfl

end MaxNN.Caterpillar
