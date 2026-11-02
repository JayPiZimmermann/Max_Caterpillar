import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Std.Tactic.Ext

/-! # Positive counts in a moving support and its stationary complement -/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction

/-- Restricting a sign predicate to a support and its complement partitions all
positive indices, without any assumption about negative or zero outputs. -/
theorem positive_count_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (s : ι → Bool) :
    (A.filter fun i => s i = true).card +
      (Aᶜ.filter fun i => s i = true).card =
        (Finset.univ.filter fun i => s i = true).card := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ.filter fun i => s i = true) (fun i => i ∈ A)
  have heA : (Finset.univ.filter (fun i => s i = true)).filter (fun i => i ∈ A) =
      A.filter (fun i => s i = true) := by
    ext i
    simp [and_comm]
  have heC : (Finset.univ.filter (fun i => s i = true)).filter (fun i => i ∉ A) =
      Aᶜ.filter (fun i => s i = true) := by
    ext i
    simp [and_comm]
  rw [heA,heC] at h
  exact h

/-- Three positive outputs in total and two in a stationary triple leave
precisely one positive output in the corresponding moving pair. -/
theorem one_positive_of_stationary_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (s : ι → Bool)
    (hP : (Finset.univ.filter fun i => s i = true).card = 3)
    (hZ : (Aᶜ.filter fun i => s i = true).card = 2) :
    (A.filter fun i => s i = true).card = 1 := by
  have h := positive_count_partition A s
  rw [hP,hZ] at h
  exact Nat.add_right_cancel (show (A.filter fun i => s i = true).card + 2 = 1 + 2 from h)

/-- The role and sign-count premises have a genuine finite instance. This checks the premises independently of any real-valued network. -/
example : ∃ (A B : Finset (Fin 5)) (s : Fin 5 → Bool),
    A.card = 2 ∧ B.card = 2 ∧ (A ∪ B).card = 3 ∧
      (Finset.univ.filter fun i => s i = true).card = 3 ∧
      (A.filter fun i => s i = true).card = 1 ∧
      (B.filter fun i => s i = true).card = 1 := by
  exact ⟨{0,1},{0,2},![true,false,false,true,true],by decide,by decide,
    by decide,by decide,by decide,by decide⟩

#print axioms positive_count_partition
#print axioms one_positive_of_stationary_two
end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
