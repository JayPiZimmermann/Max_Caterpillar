import MaxCaterpillar.Fiber.Count65.SectorQuotient.Labels

/-! The global 65-valued invariant of the actual zero-bias symmetry quotient.
Continuity and exact sector tests do not require sector connectedness. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65
open SectorQuotient

noncomputable def decodeComponentLabel (p : Option NonpairedLabel × Option NonpairedLabel) :
    ComponentLabel :=
  match p.1 with
  | some l => Sum.inr (Sum.inl l)
  | none => match p.2 with
    | some l => Sum.inr (Sum.inr l)
    | none => Sum.inl ()

noncomputable def globalLabel (z : ZeroBiasSymmetryQuotient 4 6 5) : ComponentLabel :=
  decodeComponentLabel (mixedZeroBiasLabel z,starZeroBiasLabel z)

theorem continuous_globalLabel : Continuous globalLabel :=
  (continuous_of_discreteTopology : Continuous decodeComponentLabel).comp
    (continuous_mixedZeroBiasLabel.prod_mk continuous_starZeroBiasLabel)

lemma mixed_star_labels_incompatible (z : ZeroBiasSymmetryQuotient 4 6 5)
    (l m : NonpairedLabel) (hm : mixedZeroBiasLabel z=some l)
    (hs : starZeroBiasLabel z=some m) : False := by
  induction z using Quotient.inductionOn with
  | h x =>
    have hM : includeZeroBias x∈Mixed65.sector := by
      by_contra hn
      have he := (mixedZeroBiasLabel_none_iff x).mpr hn
      rw [hm] at he
      cases he
    have hS : includeZeroBias x∈starSet := by
      by_contra hn
      have he := (starZeroBiasLabel_none_iff x).mpr hn
      rw [hs] at he
      cases he
    exact Set.disjoint_left.mp mixed_star_disjoint hM hS

lemma globalLabel_mixed (z : ZeroBiasSymmetryQuotient 4 6 5) (l : NonpairedLabel) :
    globalLabel z=Sum.inr (Sum.inl l) ↔ mixedZeroBiasLabel z=some l := by
  cases hm : mixedZeroBiasLabel z with
  | none => cases hs : starZeroBiasLabel z <;> simp [globalLabel,decodeComponentLabel,hm,hs]
  | some m => simp [globalLabel,decodeComponentLabel,hm]

lemma globalLabel_star (z : ZeroBiasSymmetryQuotient 4 6 5) (l : NonpairedLabel) :
    globalLabel z=Sum.inr (Sum.inr l) ↔ starZeroBiasLabel z=some l := by
  cases hm : mixedZeroBiasLabel z with
  | none => cases hs : starZeroBiasLabel z <;> simp [globalLabel,decodeComponentLabel,hm,hs]
  | some m =>
    have hn : starZeroBiasLabel z≠some l := mixed_star_labels_incompatible z m l hm
    simp [globalLabel,decodeComponentLabel,hm,hn]

lemma globalLabel_paired (z : ZeroBiasSymmetryQuotient 4 6 5) :
    globalLabel z=Sum.inl () ↔ mixedZeroBiasLabel z=none ∧ starZeroBiasLabel z=none := by
  cases hm : mixedZeroBiasLabel z <;> cases hs : starZeroBiasLabel z <;>
    simp [globalLabel,decodeComponentLabel,hm,hs]

/-- The default label is exactly the actual paired sector, using the proved
unconditional first-matrix partition. -/
lemma globalLabel_paired_mk (x : ZeroBiasFiber 4 6 5) :
    globalLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x)=Sum.inl () ↔
      includeZeroBias x∈pairedSet := by
  rw [globalLabel_paired,mixedZeroBiasLabel_none_iff,starZeroBiasLabel_none_iff]
  constructor
  · rintro ⟨hm,hs⟩
    by_contra hp
    have hc : includeZeroBias x∈pairedSetᶜ := hp
    rw [paired_compl_eq] at hc
    exact hc.elim hm hs
  · intro hp
    exact ⟨fun hm => Set.disjoint_left.mp paired_mixed_disjoint hp hm,
      fun hs => Set.disjoint_left.mp paired_star_disjoint hp hs⟩

/-- Explicit separation of finite-label assembly from actual point attainment.
The final public lower bound supplies all three existence proofs. -/
theorem globalLabel_surjective_of_attainment
    (hm : ∀ l : NonpairedLabel,∃ z,mixedZeroBiasLabel z=some l)
    (hs : ∀ l : NonpairedLabel,∃ z,starZeroBiasLabel z=some l)
    (hp : ∃ z,mixedZeroBiasLabel z=none ∧ starZeroBiasLabel z=none) :
    Function.Surjective globalLabel := by
  intro l
  rcases l with u | (m | s)
  · obtain ⟨z,hm,hs⟩ := hp
    exact ⟨z,(globalLabel_paired z).mpr ⟨hm,hs⟩⟩
  · obtain ⟨z,hz⟩ := hm m
    exact ⟨z,(globalLabel_mixed z m).mpr hz⟩
  · obtain ⟨z,hz⟩ := hs s
    exact ⟨z,(globalLabel_star z s).mpr hz⟩

noncomputable def componentLabelEquivFin65 : ComponentLabel ≃ Fin 65 :=
  Fintype.equivFinOfCardEq componentLabel_card

noncomputable def globalLabelFin65 : ZeroBiasSymmetryQuotient 4 6 5 → Fin 65 :=
  componentLabelEquivFin65 ∘ globalLabel

theorem continuous_globalLabelFin65 : Continuous globalLabelFin65 :=
  (continuous_of_discreteTopology : Continuous componentLabelEquivFin65).comp continuous_globalLabel

#print axioms continuous_globalLabel
#print axioms globalLabel_mixed
#print axioms globalLabel_star
#print axioms globalLabel_paired_mk
end MaxCaterpillar.Fiber.Count65
