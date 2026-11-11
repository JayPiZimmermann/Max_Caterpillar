import MaxCaterpillar.Fiber.Components

/-! # A component classification on the some-part of a discrete label map -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SomeFiberComponents
open Set Function
variable {X L : Type*} [TopologicalSpace X] [TopologicalSpace L]
    [TopologicalSpace (Option L)] [DiscreteTopology L] [DiscreteTopology (Option L)] [Inhabited L]

abbrev Sector (f : X → Option L) := {x : X // ∃ l,f x=some l}
noncomputable def label (f : X → Option L) (x : Sector f) : L := (f x.val).getD default

lemma label_spec (f : X → Option L) (x : Sector f) : f x.val=some (label f x) := by
  obtain ⟨l,hl⟩ := x.property
  simp [label,hl]

lemma label_eq_iff (f : X → Option L) (x : Sector f) (l : L) :
    label f x=l ↔ f x.val=some l := by
  constructor
  · intro h
    exact (label_spec f x).trans (congrArg some h)
  · intro h
    exact Option.some.inj ((label_spec f x).symm.trans h)

lemma continuous_label (f : X → Option L) (hf : Continuous f) : Continuous (label f) :=
  (continuous_of_discreteTopology : Continuous (fun o : Option L => o.getD default)).comp
    (hf.comp continuous_subtype_val)

lemma isPathConnected_label_fiber (f : X → Option L)
    (hc : ∀ l,IsPathConnected (f ⁻¹' {some l})) (l : L) :
    IsPathConnected (label f ⁻¹' {l}) := by
  have hi : Inducing (Subtype.val : Sector f → X) := inducing_subtype_val
  apply hi.isPathConnected_iff.mpr
  have he : (Subtype.val : Sector f → X) '' (label f ⁻¹' {l})=f ⁻¹' {some l} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (label_eq_iff f y l).mp hy
    · intro hx
      let y : Sector f := ⟨x,⟨l,hx⟩⟩
      exact ⟨y,(label_eq_iff f y l).mpr hx,rfl⟩
  rw [he]
  exact hc l

/-- An actual continuous discrete label with connected nonempty some-fibers
classifies the components of its some-sector. No finite counting is needed. -/
noncomputable def componentsEquiv (f : X → Option L) (hf : Continuous f)
    (hc : ∀ l,IsPathConnected (f ⁻¹' {some l})) : ConnectedComponents (Sector f) ≃ L := by
  have hs : Surjective (label f) := by
    intro l
    obtain ⟨x,hx,_⟩ := hc l
    let y : Sector f := ⟨x,⟨l,hx⟩⟩
    exact ⟨y,(label_eq_iff f y l).mpr hx⟩
  exact connectedComponentsEquiv (continuous_label f hf) hs
    (fun l => (isPathConnected_label_fiber f hc l).isConnected.2)

#print axioms componentsEquiv
end MaxCaterpillar.Fiber.Count65.SomeFiberComponents
