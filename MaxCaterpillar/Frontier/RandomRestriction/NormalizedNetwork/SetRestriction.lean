import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Restriction

/-! # The faithful restriction stated directly for a coordinate finset -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N h₁ h₂ : ℕ}

noncomputable def selectedEmbedding (S : Finset (Fin N)) : Fin S.card ↪ Fin N where
  toFun i := (S.equivFin.symm i).val
  inj' := by
    intro i j h
    exact S.equivFin.symm.injective (Subtype.ext h)

lemma selectedEmbedding_image (S : Finset (Fin N)) :
    Finset.univ.image (selectedEmbedding S) = S := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hi
    exact ha ▸ (S.equivFin.symm a).property
  · intro hi
    refine Finset.mem_image.mpr ⟨S.equivFin ⟨i,hi⟩,Finset.mem_univ _,?_⟩
    change (S.equivFin.symm (S.equivFin ⟨i,hi⟩)).val = i
    rw [S.equivFin.symm_apply_apply]

/-- No witness of genericity, width reduction, or normalized-model premise is
required from the caller. `NeZero S.card` states that the selected set is nonempty. -/
theorem exists_ordinary_set_restriction [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (S : Finset (Fin N)) [NeZero S.card] :
    ∃ model : NormalizedNetwork S.card h₁ h₂,
      (∀ x, model.eval x = Maximum S.card x) ∧ model.TranslationNormalized ∧
      (∀ j, model.A j = if (∑ i, net.W₁ j i) = 0 ∧ rowSupport (net.W₁ j) ⊆ S
        then restrict (selectedEmbedding S) (net.W₁ j) else 0) ∧
      (∀ j, model.Feeding j → ∃ k, net.W₂ k j ≠ 0) ∧
      (∀ cost : ℕ → ℕ,
        (∑ j, if 3 ≤ (rowSupport (model.A j)).card
          then cost (rowSupport (model.A j)).card else 0) ≤
        ∑ j, if 3 ≤ (rowSupport (net.W₁ j)).card ∧ rowSupport (net.W₁ j) ⊆ S
          then cost (rowSupport (net.W₁ j)).card else 0) := by
  simpa only [selectedEmbedding_image] using
    exists_ordinary_restriction net hnet (selectedEmbedding S)

#check @exists_ordinary_set_restriction
#print axioms exists_ordinary_set_restriction
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
