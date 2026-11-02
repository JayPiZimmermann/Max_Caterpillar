import MaxCaterpillar.Fiber.Components
import MaxCaterpillar.Fiber.BiasQuotient
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

/-!
# Component labels and quotient assembly for the proposed (6,5) classification

This file does not assert the network component count. The finite label count
and the topological passage through the genuine symmetry relation are distinct
from constructing a continuous, exhaustive actual-network classification.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open Set Function

/-- Residual branch, three correction orientations, and reconstruction type. -/
abbrev NonpairedLabel := Bool × (Fin 3 → Bool) × Bool

/-- One paired label and the two nonpaired families. This is a label type only. -/
abbrev ComponentLabel := Unit ⊕ (NonpairedLabel ⊕ NonpairedLabel)

theorem nonpairedLabel_card : Fintype.card NonpairedLabel = 32 := by decide
theorem componentLabel_card : Fintype.card ComponentLabel = 65 := by decide

section QuotientClassification
universe u v
variable {X : Type u} {L : Type v} [TopologicalSpace X] [TopologicalSpace L]
    [DiscreteTopology L]

/-- Any quotient of a discrete label space retains its canonical discrete topology. -/
instance discreteTopology_quotient_labels (s : Setoid L) :
    DiscreteTopology (Quotient s) := by
  apply forall_open_iff_discrete.mp
  intro t
  change IsOpen ((Quotient.mk s) ⁻¹' t)
  exact isOpen_discrete _

/-- A continuous discrete classification descends through compatible relations.
The lifting condition is a concrete symmetry action on labels, not path lifting. -/
noncomputable def quotientLabel (sX : Setoid X) (sL : Setoid L)
    (label : X → L)
    (hrespect : ∀ x y, sX.r x y → sL.r (label x) (label y)) :
    Quotient sX → Quotient sL :=
  Quotient.map' label hrespect

lemma quotientLabel_continuous (sX : Setoid X) (sL : Setoid L)
    (label : X → L) (hcont : Continuous label)
    (hrespect : ∀ x y, sX.r x y → sL.r (label x) (label y)) :
    Continuous (quotientLabel sX sL label hrespect) :=
  hcont.quotient_map' _

/-- A descended label fiber is the continuous image of one connected raw label
fiber, provided every equivalent label can be reached by an actual symmetry. -/
lemma quotientLabel_fiber (sX : Setoid X) (sL : Setoid L)
    (label : X → L)
    (hrespect : ∀ x y, sX.r x y → sL.r (label x) (label y))
    (hlift : ∀ x l, sL.r (label x) l → ∃ y, sX.r x y ∧ label y = l)
    (l : L) :
    (quotientLabel sX sL label hrespect) ⁻¹' {Quotient.mk sL l} =
      Quotient.mk sX '' (label ⁻¹' {l}) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := Quot.exists_rep q
    change Quotient.mk sL (label x) = Quotient.mk sL l at hq
    obtain ⟨y, hxy, hy⟩ := hlift x l (Quotient.exact hq)
    exact ⟨y, hy, (Quotient.sound hxy).symm⟩
  · rintro ⟨x, hx, rfl⟩
    change Quotient.mk sL (label x) = Quotient.mk sL l
    exact congrArg (Quotient.mk sL) hx

/-- Symmetry-compatible connected raw classes yield an exact classification of
components of the actual quotient. No quotient-path lifting is assumed. -/
noncomputable def quotientComponentsEquiv (sX : Setoid X) (sL : Setoid L)
    (label : X → L) (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l}))
    (hrespect : ∀ x y, sX.r x y → sL.r (label x) (label y))
    (hlift : ∀ x l, sL.r (label x) l → ∃ y, sX.r x y ∧ label y = l) :
    ConnectedComponents (Quotient sX) ≃ Quotient sL := by
  let q := quotientLabel sX sL label hrespect
  have hqcont : Continuous q := quotientLabel_continuous sX sL label hcont hrespect
  have hqsurj : Surjective q := by
    intro z
    obtain ⟨l, rfl⟩ := Quot.exists_rep z
    obtain ⟨x, rfl⟩ := hsurj l
    exact ⟨Quotient.mk sX x, rfl⟩
  have hqfib : ∀ z, IsPreconnected (q ⁻¹' {z}) := by
    intro z
    obtain ⟨l, rfl⟩ := Quot.exists_rep z
    change IsPreconnected ((quotientLabel sX sL label hrespect) ⁻¹' {Quotient.mk sL l})
    rw [quotientLabel_fiber sX sL label hrespect hlift]
    exact (hfib l).image _ continuous_quotient_mk'.continuousOn
  exact connectedComponentsEquiv hqcont hqsurj hqfib

end QuotientClassification
/-- A faithful parameter homeomorphism transports the actual connected-component
space. This supplies the coefficient-to-function-space bridge used by the heads. -/
noncomputable def connectedComponentsEquivOfHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y :=
  connectedComponentsEquivOfRetraction e e.symm e.continuous_toFun
    e.symm.continuous_toFun e.apply_symm_apply (fun x => by
      rw [e.symm_apply_apply]
      exact mem_connectedComponent)

noncomputable def connectedComponentsHomeomorphOfHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  connectedComponentsHomeomorphOfRetraction e e.symm e.continuous_toFun
    e.symm.continuous_toFun e.apply_symm_apply (fun x => by
      rw [e.symm_apply_apply]
      exact mem_connectedComponent)

#check @quotientComponentsEquiv
#print axioms nonpairedLabel_card
#print axioms componentLabel_card
#print axioms quotientComponentsEquiv
#print axioms connectedComponentsEquivOfHomeomorph
end MaxCaterpillar.Fiber.Count65
