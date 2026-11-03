import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! Literal induced-component count at most two gives one connected set,
or a disjoint union of two nonempty connected induced sets. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo
open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- A graph component is connected as an induced graph on its actual support. -/
lemma component_support_connected {V : Type*} (G : SimpleGraph V)
    (c : G.ConnectedComponent) : (G.induce c.supp).Connected := by
  classical
  induction c using ConnectedComponent.ind with
  | h u =>
    apply G.induce_connected_of_patches u (by rfl)
    intro v hv
    have hr : G.Reachable u v :=
      (ConnectedComponent.exact hv).symm
    obtain ⟨p⟩ := hr
    refine ⟨{z | z∈p.support},?_,p.start_mem_support,p.end_mem_support,?_⟩
    · intro z hz
      exact (ConnectedComponent.sound (p.takeUntil z hz).reachable).symm
    · exact p.connected_induce_support ⟨u,p.start_mem_support⟩ ⟨v,p.end_mem_support⟩

variable {N : ℕ}

/-- Original labels in one component of an induced graph. -/
def componentVertices (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (c : (G.induce (S : Set (Fin N))).ConnectedComponent) : Finset (Fin N) :=
  S.filter fun v => ∃ hv : v∈S, (G.induce (S : Set (Fin N))).connectedComponentMk ⟨v,hv⟩=c

@[simp] lemma mem_componentVertices (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (c : (G.induce (S : Set (Fin N))).ConnectedComponent) (v : Fin N) :
    v∈componentVertices G S c ↔
      ∃ hv : v∈S, (G.induce (S : Set (Fin N))).connectedComponentMk ⟨v,hv⟩=c := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hv,hc⟩
    exact Finset.mem_filter.mpr ⟨hv,hv,hc⟩

lemma componentVertices_subset (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (c : (G.induce (S : Set (Fin N))).ConnectedComponent) :
    componentVertices G S c⊆S := Finset.filter_subset _ _

lemma componentVertices_nonempty (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (c : (G.induce (S : Set (Fin N))).ConnectedComponent) :
    (componentVertices G S c).Nonempty := by
  induction c using ConnectedComponent.ind with
  | h v => exact ⟨v.val,(mem_componentVertices G S _ _).mpr ⟨v.property,rfl⟩⟩

lemma componentVertices_disjoint (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (c d : (G.induce (S : Set (Fin N))).ConnectedComponent) (hcd : c≠d) :
    Disjoint (componentVertices G S c) (componentVertices G S d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hc hd
  obtain ⟨hv,hc⟩ := (mem_componentVertices G S c v).mp hc
  obtain ⟨_,hd⟩ := (mem_componentVertices G S d v).mp hd
  exact hcd (hc.symm.trans hd)

lemma componentVertices_connected (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (c : (G.induce (S : Set (Fin N))).ConnectedComponent) :
    (G.induce (componentVertices G S c : Set (Fin N))).Connected := by
  let H := G.induce (S : Set (Fin N))
  let f : H.induce c.supp →g G.induce (componentVertices G S c : Set (Fin N)) :=
    { toFun := fun v => ⟨v.val.val,(mem_componentVertices G S c v.val.val).mpr
        ⟨v.val.property,v.property⟩⟩
      map_rel' := fun {u v} h => h }
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨hv,hc⟩ := (mem_componentVertices G S c v.val).mp v.property
    refine ⟨⟨⟨v.val,hv⟩,hc⟩,?_⟩
    apply Subtype.ext
    rfl
  exact Connected.map f hf (component_support_connected H c)

/-- At most two literal induced components (including isolated vertices)
means connected, or a disjoint union of two nonempty connected induced sets.
No bound on degrees is assumed in this decomposition. -/
theorem two_components_decomposition (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty)
    (hc : Nat.card (G.induce (S : Set (Fin N))).ConnectedComponent≤2) :
    (G.induce (S : Set (Fin N))).Connected ∨
      ∃ A B : Finset (Fin N), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
        S=A∪B ∧ (G.induce (A : Set (Fin N))).Connected ∧
        (G.induce (B : Set (Fin N))).Connected := by
  classical
  let H := G.induce (S : Set (Fin N))
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hc' : Fintype.card H.ConnectedComponent≤2 := by
    simpa only [Nat.card_eq_fintype_card] using hc
  obtain ⟨u,hu⟩ := hS
  let c : H.ConnectedComponent := H.connectedComponentMk ⟨u,hu⟩
  by_cases hd : ∃ d : H.ConnectedComponent,d≠c
  · obtain ⟨d,hd⟩ := hd
    have htwo : ∀ e : H.ConnectedComponent,e=c ∨ e=d := by
      intro e
      by_contra he
      push_neg at he
      have hlarge : 2<Fintype.card H.ConnectedComponent :=
        Fintype.two_lt_card_iff.mpr ⟨c,d,e,Ne.symm hd,Ne.symm he.1,Ne.symm he.2⟩
      exact (not_lt_of_ge hc') hlarge
    right
    refine ⟨componentVertices G S c,componentVertices G S d,
      componentVertices_nonempty G S c,componentVertices_nonempty G S d,
      componentVertices_disjoint G S c d (Ne.symm hd),?_,
      componentVertices_connected G S c,componentVertices_connected G S d⟩
    ext v
    constructor
    · intro hv
      rcases htwo (H.connectedComponentMk ⟨v,hv⟩) with h|h
      · exact Finset.mem_union.mpr (Or.inl ((mem_componentVertices G S c v).mpr ⟨hv,h⟩))
      · exact Finset.mem_union.mpr (Or.inr ((mem_componentVertices G S d v).mpr ⟨hv,h⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with h|h
      · exact componentVertices_subset G S c h
      · exact componentVertices_subset G S d h
  · left
    have heq : componentVertices G S c=S := by
      apply Finset.Subset.antisymm (componentVertices_subset G S c)
      intro v hv
      apply (mem_componentVertices G S c v).mpr
      exact ⟨hv,by by_contra h; exact hd ⟨H.connectedComponentMk ⟨v,hv⟩,h⟩⟩
    have hconn := componentVertices_connected G S c
    rwa [heq] at hconn

#print axioms component_support_connected
#print axioms componentVertices_connected
#print axioms two_components_decomposition
end MaxCaterpillar.ExponentialPush.DegreeTwo
