import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Defs
import Mathlib.Algebra.BigOperators.Basic

/-!
# Reusable finite combinatorics for spine quotients

This file isolates two bookkeeping facts used by the canonical spine model:
an injective map identifies a finset with its image, and uniformly large
fibers bound the size of a finite image.
-/

namespace MaxNN.Caterpillar.Corrections

open scoped BigOperators

/-- An injective map gives the canonical equivalence between a finset and its
image. -/
noncomputable def finsetImageEquiv {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (hf : Function.Injective f) : ↑s ≃ ↑(s.image f) :=
  Equiv.ofBijective
    (fun x : ↑s => ⟨f x, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩)
    ⟨fun x y h => Subtype.ext (hf (congrArg Subtype.val h)), by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩⟩

@[simp] theorem finsetImageEquiv_apply {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (hf : Function.Injective f) (x : ↑s) :
    (finsetImageEquiv s f hf x).1 = f x.1 := rfl

/-- A uniform lower bound on the nonempty fibers of a map bounds the size of
its finite image. -/
theorem card_image_mul_le_of_fiber_card {I A : Type*} [Fintype I]
    [DecidableEq A] (m : ℕ) (f : I → A)
    (hfiber : ∀ a ∈ Finset.univ.image f,
      m ≤ (Finset.univ.filter fun i => f i = a).card) :
    m * (Finset.univ.image f).card ≤ Fintype.card I := by
  calc
    m * (Finset.univ.image f).card =
        ∑ _a in Finset.univ.image f, m := by simp [Nat.mul_comm]
    _ ≤ ∑ a in Finset.univ.image f,
        (Finset.univ.filter fun i => f i = a).card := Finset.sum_le_sum hfiber
    _ = Finset.univ.card := (Finset.card_eq_sum_card_fiberwise
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)).symm
    _ = Fintype.card I := Finset.card_univ

end MaxNN.Caterpillar.Corrections
