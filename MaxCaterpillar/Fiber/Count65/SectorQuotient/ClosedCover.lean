import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Constructions

/-! Continuous descent from a finite closed cover with verified transition
consistency. No orbit or normalization identification is added by definition. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient
open Set

variable {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite I]

noncomputable def closedCoverGlue (C : I → Set X) (cover : ∀ x,∃ i,x∈C i)
    (f : ∀ i,C i → Y) : X → Y :=
  fun x => f (Classical.choose (cover x)) ⟨x,Classical.choose_spec (cover x)⟩

lemma closedCoverGlue_eq (C : I → Set X) (cover : ∀ x,∃ i,x∈C i)
    (f : ∀ i,C i → Y)
    (compatible : ∀ i j (x : X) (hi : x∈C i) (hj : x∈C j),f i ⟨x,hi⟩=f j ⟨x,hj⟩)
    (i : I) (x : C i) : closedCoverGlue C cover f x=f i x :=
  compatible _ _ x (Classical.choose_spec (cover x)) x.property

/-- Finite closed-cover gluing is continuous once the actual transition
identities have been supplied and checked. -/
theorem continuous_closedCoverGlue (C : I → Set X) (cover : ∀ x,∃ i,x∈C i)
    (closed : ∀ i,IsClosed (C i)) (f : ∀ i,C i → Y)
    (continuous_f : ∀ i,Continuous (f i))
    (compatible : ∀ i j (x : X) (hi : x∈C i) (hj : x∈C j),f i ⟨x,hi⟩=f j ⟨x,hj⟩) :
    Continuous (closedCoverGlue C cover f) := by
  have hc : ⋃ i,C i=univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    exact cover x
  apply (locallyFinite_of_finite C).continuous hc closed
  intro i
  rw [continuousOn_iff_continuous_restrict]
  have heq : (fun x : C i => closedCoverGlue C cover f x)=f i := by
    funext x
    exact closedCoverGlue_eq C cover f compatible i x
  change Continuous (fun x : C i => closedCoverGlue C cover f x)
  rw [heq]
  exact continuous_f i

#print axioms continuous_closedCoverGlue
end MaxCaterpillar.Fiber.Count65.SectorQuotient
