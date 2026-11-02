import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.CarrierPair
import MaxCaterpillar.Fiber.Symmetry
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment

/-- Representatives for each nonempty member of a four-way partition can be
placed in four distinct physical slots. Empty groups receive a spare slot. -/
theorem fourGroup_roles (group : Fin 4 → Fin 4) :
    ∃ e : Equiv.Perm (Fin 4), ∀ i,
      (∃ j, group j=i) → group (e i)=i := by
  classical
  let reps : Set (Fin 4) := Set.range group
  have hsurj : Function.Surjective (fun j : Fin 4 => (⟨group j, ⟨j,rfl⟩⟩ : reps)) := by
    rintro ⟨i,j,hj⟩
    exact ⟨j, Subtype.ext hj⟩
  let f : reps → Fin 4 := Function.surjInv hsurj
  have hf : Function.Injective f := Function.injective_surjInv hsurj
  let emb : reps ↪ Fin 4 := ⟨f,hf⟩
  let ee : reps ≃ Set.range emb := Function.Embedding.toEquivRange emb
  let e : Equiv.Perm (Fin 4) := ee.extendSubtype
  have he : ∀ i : reps, e i=f i := by
    intro i
    exact ee.extendSubtype_apply_of_mem i i.property
  refine ⟨e,fun i hi => ?_⟩
  have hi' : i∈reps := hi
  have hh := Function.surjInv_eq hsurj (⟨i,hi'⟩ : reps)
  have he' := he (⟨i,hi'⟩ : reps)
  change e i=f ⟨i,hi'⟩ at he'
  rw [he']
  exact congrArg Subtype.val hh

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
