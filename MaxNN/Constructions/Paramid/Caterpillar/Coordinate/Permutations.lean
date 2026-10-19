import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Weights
import Mathlib.GroupTheory.Perm.Fin

/-! # Deleting the distinguished coordinate vertex from a permutation -/

namespace MaxNN.Caterpillar

/-- Insert the distinguished label `0` at position `p`, while the remaining
labels occur in the order prescribed by `π`. -/
def insertZeroPerm {n : ℕ} (p : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquiv' p).trans (Equiv.optionCongr π)).trans (finSuccEquiv' 0).symm

@[simp] theorem insertZeroPerm_at {n : ℕ} (p : Fin (n + 1))
    (π : Equiv.Perm (Fin n)) : insertZeroPerm p π p = 0 := by
  simp [insertZeroPerm]

@[simp] theorem insertZeroPerm_lift {n : ℕ} (p : Fin (n + 1))
    (π : Equiv.Perm (Fin n)) (q : Fin n) :
    insertZeroPerm p π (p.succAbove q) = (π q).succ := by
  simp [insertZeroPerm]

theorem insertZeroPerm_injective {n : ℕ} :
    Function.Injective (fun q : Fin (n + 1) × Equiv.Perm (Fin n) =>
      insertZeroPerm q.1 q.2) := by
  rintro ⟨p, π⟩ ⟨q, τ⟩ h
  have hp : p = q := by
    have hz : insertZeroPerm p π p = insertZeroPerm q τ p :=
      congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e p) h
    rw [insertZeroPerm_at] at hz
    have : insertZeroPerm q τ p = insertZeroPerm q τ q := by
      rw [insertZeroPerm_at]
      exact hz.symm
    exact (insertZeroPerm q τ).injective this
  subst q
  change insertZeroPerm p π = insertZeroPerm p τ at h
  have hπτ : π = τ := by
    apply Equiv.ext
    intro a
    apply Fin.succ_injective n
    rw [← insertZeroPerm_lift p π a, ← insertZeroPerm_lift p τ a]
    exact congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e (p.succAbove a)) h
  subst τ
  rfl

/-- Every permutation has a unique position of `0` and a unique ordering of
the remaining labels. -/
noncomputable def insertZeroEquiv (n : ℕ) :
    (Fin (n + 1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun q => insertZeroPerm q.1 q.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨insertZeroPerm_injective,
        (Fintype.card_congr (Equiv.Perm.decomposeFin (n := n))).symm⟩)

@[simp] theorem insertZeroEquiv_apply (n : ℕ)
    (q : Fin (n + 1) × Equiv.Perm (Fin n)) :
    insertZeroEquiv n q = insertZeroPerm q.1 q.2 := rfl

end MaxNN.Caterpillar
