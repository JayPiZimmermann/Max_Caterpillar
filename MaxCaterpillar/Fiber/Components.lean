import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homeomorph
import Mathlib.SetTheory.Cardinal.Finite

/-! # Counting components from an exact discrete classification

The classification map in this file is a map from the actual topological space being
classified. Continuity, surjectivity, and preconnectedness of every label fiber are
separate hypotheses. In particular, counting labels alone is not a component-count
theorem for a network parameter fiber.

The results apply to a symmetry quotient once that quotient and its classification
map have been constructed. They do not assume that paths in a quotient lift.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open Set Function

universe u v

variable {X : Type u} {L : Type v} [TopologicalSpace X] [TopologicalSpace L]

/-- Open label fibers suffice for continuity. Thus a proof by clopen sectors
can supply the continuity obligation without assuming a parameterization. -/
theorem continuous_of_open_label_fibers {label : X → L}
    (hopen : ∀ l, IsOpen (label ⁻¹' {l})) : Continuous label := by
  apply continuous_def.mpr
  intro s _hs
  have heq : label ⁻¹' s = ⋃ l ∈ s, label ⁻¹' {l} := by
    ext x
    simp
  rw [heq]
  exact isOpen_iUnion fun l => isOpen_iUnion fun _ => hopen l

/-- A continuous invariant with preconnected fibers distinguishes exactly the
connected components when its target is totally disconnected. -/
theorem connectedComponent_eq_iff_label_eq [TotallyDisconnectedSpace L]
    {label : X → L} (hcont : Continuous label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) (x y : X) :
    connectedComponent x = connectedComponent y ↔ label x = label y := by
  constructor
  · exact hcont.image_eq_of_connectedComponent_eq x y
  · intro hxy
    apply connectedComponent_eq
    apply (hfib (label x)).subset_connectedComponent
    · exact Set.mem_preimage.mpr rfl
    · exact Set.mem_preimage.mpr hxy.symm

/-- Each fiber of the classification map is the full connected component,
including all boundary points of the original topological space. -/
theorem connectedComponent_eq_label_fiber [TotallyDisconnectedSpace L]
    {label : X → L} (hcont : Continuous label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) (x : X) :
    connectedComponent x = label ⁻¹' {label x} := by
  ext y
  constructor
  · intro hy
    exact Set.mem_preimage.mpr
      (hcont.image_eq_of_connectedComponent_eq y x (connectedComponent_eq hy).symm)
  · intro hy
    exact (hfib (label x)).subset_connectedComponent (Set.mem_preimage.mpr rfl) hy

/-- The induced map on connected components is bijective precisely from the
three classification obligations used here: continuity, existence of every label,
and preconnectedness of every fiber. -/
theorem connectedComponentsLift_bijective [TotallyDisconnectedSpace L]
    {label : X → L} (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) :
    Bijective hcont.connectedComponentsLift := by
  constructor
  · intro q r hqr
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe r
    apply ConnectedComponents.coe_eq_coe.mpr
    exact (connectedComponent_eq_iff_label_eq hcont hfib x y).mpr hqr
  · intro l
    obtain ⟨x, hx⟩ := hsurj l
    exact ⟨(x : ConnectedComponents X), hx⟩

/-- The exact classification equivalence, rather than only a cardinality bound. -/
noncomputable def connectedComponentsEquiv [TotallyDisconnectedSpace L]
    {label : X → L} (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) : ConnectedComponents X ≃ L :=
  Equiv.ofBijective hcont.connectedComponentsLift
    (connectedComponentsLift_bijective hcont hsurj hfib)

/-- For discrete labels, the classification also describes the topology of the
space of connected components. No local path-connectedness hypothesis is needed. -/
noncomputable def connectedComponentsHomeomorph [DiscreteTopology L]
    {label : X → L} (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) : ConnectedComponents X ≃ₜ L where
  toEquiv := connectedComponentsEquiv hcont hsurj hfib
  continuous_toFun := hcont.connectedComponentsLift_continuous
  continuous_invFun := continuous_of_discreteTopology

/-- A finite exhaustive component classification gives the exact component count. -/
theorem card_connectedComponents [TotallyDisconnectedSpace L] [Finite L]
    {label : X → L} (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) :
    Nat.card (ConnectedComponents X) = Nat.card L :=
  Nat.card_congr (connectedComponentsEquiv hcont hsurj hfib)

/-- A finite label classification gives an equivalence with `Fin n` itself.
Unlike an isolated natural cardinality equation, this formulation also records
finiteness when the asserted count is zero. -/
theorem nonempty_componentsEquiv_fin [TotallyDisconnectedSpace L] [Finite L]
    {label : X → L} (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPreconnected (label ⁻¹' {l})) {n : ℕ}
    (hcard : Nat.card L = n) : Nonempty (ConnectedComponents X ≃ Fin n) := by
  classical
  letI := Fintype.ofFinite L
  have hc : Fintype.card L = n := by simpa only [Nat.card_eq_fintype_card] using hcard
  exact ⟨(connectedComponentsEquiv hcont hsurj hfib).trans (Fintype.equivFinOfCardEq hc)⟩

/-- A path-connected classification is sufficient for the same exact connected
component count. The hypotheses still concern all points of every label fiber. -/
theorem card_connectedComponents_of_pathConnected_fibers
    [TotallyDisconnectedSpace L] [Finite L]
    {label : X → L} (hcont : Continuous label) (hsurj : Surjective label)
    (hfib : ∀ l, IsPathConnected (label ⁻¹' {l})) :
    Nat.card (ConnectedComponents X) = Nat.card L :=
  card_connectedComponents hcont hsurj (fun l => (hfib l).isConnected.2)

/-- A quotient map with connected fibers induces a bijection on connected
components. This theorem does not require, or assert, path lifting. -/
theorem connectedComponentsMap_bijective_of_connected_fibers
    {q : X → L} (hq : QuotientMap q) (hfib : ∀ l, IsConnected (q ⁻¹' {l})) :
    Bijective hq.continuous.connectedComponentsMap := by
  constructor
  · intro c d hcd
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
    change (q x : ConnectedComponents L) = (q y : ConnectedComponents L) at hcd
    have hcomp := ConnectedComponents.coe_eq_coe.mp hcd
    apply ConnectedComponents.coe_eq_coe.mpr
    apply connectedComponent_eq_iff_mem.mpr
    rw [← hq.preimage_connectedComponent hfib y]
    change q x ∈ connectedComponent (q y)
    rw [← hcomp]
    exact mem_connectedComponent
  · intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨x, rfl⟩ := hq.surjective y
    exact ⟨(x : ConnectedComponents X), rfl⟩

/-- The equivalence on connected components induced by a quotient with
connected fibers, including quotients with nonclosed individual orbits. -/
noncomputable def connectedComponentsEquivOfConnectedFibers
    {q : X → L} (hq : QuotientMap q) (hfib : ∀ l, IsConnected (q ⁻¹' {l})) :
    ConnectedComponents X ≃ ConnectedComponents L :=
  Equiv.ofBijective hq.continuous.connectedComponentsMap
    (connectedComponentsMap_bijective_of_connected_fibers hq hfib)

/-- Connected-fiber quotients preserve component cardinality. -/
theorem card_connectedComponents_of_connected_fibers
    {q : X → L} (hq : QuotientMap q) (hfib : ∀ l, IsConnected (q ⁻¹' {l})) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents L) :=
  Nat.card_congr (connectedComponentsEquivOfConnectedFibers hq hfib)

end MaxCaterpillar.Fiber
