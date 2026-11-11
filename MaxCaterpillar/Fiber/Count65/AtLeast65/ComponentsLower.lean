import MaxCaterpillar.Fiber.Count65.AtLeast65.GlobalLabel

/-! A continuous surjective finite invariant supplies distinct actual connected
components, with no finiteness or connected-fiber assumption. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65

noncomputable def zeroBiasComponentProjection65 :
    ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5) → Fin 65 :=
  continuous_globalLabelFin65.connectedComponentsLift

lemma zeroBiasComponentProjection65_mk (z : ZeroBiasSymmetryQuotient 4 6 5) :
    zeroBiasComponentProjection65 (z : ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5))=
      globalLabelFin65 z := continuous_globalLabelFin65.connectedComponentsLift_apply_coe z

lemma zeroBiasComponentProjection65_surjective_of_label
    (h : Function.Surjective globalLabelFin65) : Function.Surjective zeroBiasComponentProjection65 := by
  intro l
  obtain ⟨z,hz⟩ := h l
  exact ⟨(z : ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5)),
    (zeroBiasComponentProjection65_mk z).trans hz⟩

noncomputable def fullComponentProjection65 :
    ConnectedComponents (SymmetryQuotient 4 6 5) → Fin 65 :=
  zeroBiasComponentProjection65 ∘ zeroBiasQuotientConnectedComponentsEquiv

lemma fullComponentProjection65_surjective_of_label
    (h : Function.Surjective globalLabelFin65) : Function.Surjective fullComponentProjection65 :=
  (zeroBiasComponentProjection65_surjective_of_label h).comp
    zeroBiasQuotientConnectedComponentsEquiv.surjective

noncomputable def zeroBiasComponentsEmbedding65_of_label
    (h : Function.Surjective globalLabelFin65) :
    Fin 65 ↪ ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5) :=
  Function.Embedding.ofSurjective zeroBiasComponentProjection65
    (zeroBiasComponentProjection65_surjective_of_label h)

noncomputable def fullComponentsEmbedding65_of_label
    (h : Function.Surjective globalLabelFin65) :
    Fin 65 ↪ ConnectedComponents (SymmetryQuotient 4 6 5) :=
  Function.Embedding.ofSurjective fullComponentProjection65
    (fullComponentProjection65_surjective_of_label h)

lemma zeroBias_components_cardinal_lower_of_label
    (h : Function.Surjective globalLabelFin65) :
    (65 : Cardinal) ≤ Cardinal.mk (ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5)) := by
  simpa only [Cardinal.mk_fin] using
    Cardinal.mk_le_of_injective (zeroBiasComponentsEmbedding65_of_label h).injective

lemma full_components_cardinal_lower_of_label
    (h : Function.Surjective globalLabelFin65) :
    (65 : Cardinal) ≤ Cardinal.mk (ConnectedComponents (SymmetryQuotient 4 6 5)) := by
  simpa only [Cardinal.mk_fin] using
    Cardinal.mk_le_of_injective (fullComponentsEmbedding65_of_label h).injective

#print axioms fullComponentProjection65_surjective_of_label
#print axioms full_components_cardinal_lower_of_label
end MaxCaterpillar.Fiber.Count65
