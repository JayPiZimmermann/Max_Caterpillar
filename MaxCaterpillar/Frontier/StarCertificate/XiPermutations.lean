import MaxCaterpillar.Frontier.StarCertificate.XiSelectors
import Mathlib.Data.Fintype.Perm

/-! # The selector permutation table enumerates all input permutations

Only the finite Nat/Fin table is checked by `decide`. Its interpreted rows
are genuine equivalences, and the sum reindexing has an arbitrary additive
codomain. No claim about rational selector arithmetic is decided here.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem permutationTable_bijective : ∀ p : Fin 120,
    Function.Bijective (permutationTable p) := by decide

theorem permutationTable_injective : Function.Injective permutationTable := by decide

noncomputable def enumeratedPermutation (p : Fin 120) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (permutationTable p) (permutationTable_bijective p)

@[simp] theorem enumeratedPermutation_apply (p : Fin 120) (i : Fin 5) :
    enumeratedPermutation p i = permutationTable p i := rfl

theorem enumeratedPermutation_injective : Function.Injective enumeratedPermutation := by
  intro p q hpq
  apply permutationTable_injective
  funext i
  exact congrArg (fun e : Equiv.Perm (Fin 5) => e i) hpq

theorem enumeratedPermutation_bijective : Function.Bijective enumeratedPermutation := by
  apply (Fintype.bijective_iff_injective_and_card enumeratedPermutation).mpr
  refine ⟨enumeratedPermutation_injective,?_⟩
  rw [Fintype.card_fin,Fintype.card_perm,Fintype.card_fin]
  decide

noncomputable def permutationEquiv : Fin 120 ≃ Equiv.Perm (Fin 5) :=
  Equiv.ofBijective enumeratedPermutation enumeratedPermutation_bijective

@[simp] theorem permutationEquiv_apply (p : Fin 120) (i : Fin 5) :
    permutationEquiv p i = permutationTable p i := rfl

/-- Reindex every sum over the literal table as a sum over all permutations. -/
theorem sum_permutationTable {R : Type*} [AddCommMonoid R]
    (f : Equiv.Perm (Fin 5) → R) :
    (∑ p : Fin 120,f (permutationEquiv p)) = ∑ e : Equiv.Perm (Fin 5),f e :=
  Fintype.sum_equiv permutationEquiv _ _ (fun _ => rfl)

#print axioms permutationTable_bijective
#print axioms permutationTable_injective
#print axioms enumeratedPermutation_bijective
#print axioms sum_permutationTable
end MaxCaterpillar.Frontier.StarCertificate
