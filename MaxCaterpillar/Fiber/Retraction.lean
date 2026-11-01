import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.PathConnected

/-! # Connected components under a deformation retraction

The hypotheses are stated for actual continuous maps between the original topological
spaces. No normal-form model or connected-component classification is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous retraction induces a bijection on connected components if every point
and its retracted image lie in the same connected component of the original space. -/
noncomputable def connectedComponentsEquivOfRetraction
    (r : X → Y) (i : Y → X) (hr : Continuous r) (hi : Continuous i)
    (hri : ∀ y, r (i y) = y)
    (hir : ∀ x, i (r x) ∈ connectedComponent x) :
    ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := hr.connectedComponentsMap
  invFun := hi.connectedComponentsMap
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    change (i (r x) : ConnectedComponents X) = (x : ConnectedComponents X)
    exact ConnectedComponents.coe_eq_coe'.2 (hir x)
  right_inv := by
    intro q
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
    change (r (i y) : ConnectedComponents Y) = (y : ConnectedComponents Y)
    rw [hri]

/-- The component bijection of a deformation retraction respects the quotient topologies
on the spaces of connected components. -/
noncomputable def connectedComponentsHomeomorphOfRetraction
    (r : X → Y) (i : Y → X) (hr : Continuous r) (hi : Continuous i)
    (hri : ∀ y, r (i y) = y)
    (hir : ∀ x, i (r x) ∈ connectedComponent x) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y where
  toEquiv := connectedComponentsEquivOfRetraction r i hr hi hri hir
  continuous_toFun := hr.connectedComponentsMap_continuous
  continuous_invFun := hi.connectedComponentsMap_continuous

/-- A path from a point to its retracted image supplies the component hypothesis. -/
noncomputable def connectedComponentsEquivOfPathRetraction
    (r : X → Y) (i : Y → X) (hr : Continuous r) (hi : Continuous i)
    (hri : ∀ y, r (i y) = y)
    (hir : ∀ x, Nonempty (Path x (i (r x)))) :
    ConnectedComponents X ≃ ConnectedComponents Y :=
  connectedComponentsEquivOfRetraction r i hr hi hri
    (fun x => pathComponent_subset_component x (hir x))

end MaxCaterpillar.Fiber
