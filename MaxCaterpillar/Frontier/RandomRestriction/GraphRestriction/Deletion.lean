import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic

/-! # Actual graph edges after deleting vertices

The retained set consists of the original unordered edges with both endpoints
outside the deletion set. Its cardinality equals the edge cardinality of the
actual induced graph, including any injective relabeling of the complement.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
open BigOperators

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

noncomputable def retainedEdges (S : Finset (Fin N)) : Finset (Sym2 (Fin N)) := by
  classical
  exact G.edgeFinset.filter fun e => ∀ v, v ∈ e → v ∉ S

@[simp] theorem mem_retainedEdges (S : Finset (Fin N)) (e : Sym2 (Fin N)) :
    e ∈ retainedEdges G S ↔ e ∈ G.edgeFinset ∧ ∀ v, v ∈ e → v ∉ S := by
  classical
  simp only [retainedEdges,Finset.mem_filter]

/-- Deleting any vertex set loses at most the sum of its incidence counts,
and each incidence count is at most N−1. No disjointness is assumed between
the incident-edge sets, so edges internal to the deleted set cause no issue. -/
theorem edge_card_le_retained_add (S : Finset (Fin N)) :
    G.edgeFinset.card ≤ (retainedEdges G S).card + S.card*(N-1) := by
  classical
  have hcover : G.edgeFinset ⊆ retainedEdges G S ∪ S.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    by_cases hkeep : ∀ v, v ∈ e → v ∉ S
    · exact Finset.mem_union.mpr (Or.inl ((mem_retainedEdges G S e).mpr ⟨he,hkeep⟩))
    · push_neg at hkeep
      obtain ⟨v,hve,hvS⟩ := hkeep
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨v,hvS,?_⟩
      rw [G.mem_incidenceFinset]
      exact ⟨SimpleGraph.mem_edgeFinset.mp he,hve⟩
  have hdegree (v : Fin N) : (G.incidenceFinset v).card ≤ N-1 := by
    rw [G.card_incidenceFinset_eq_degree]
    apply Nat.le_sub_one_of_lt
    simpa only [Fintype.card_fin] using G.degree_lt_card_verts v
  have hdeleted : (S.biUnion (fun v => G.incidenceFinset v)).card ≤ S.card*(N-1) :=
    Finset.card_biUnion_le_card_mul S _ _ (fun v _ => hdegree v)
  calc
    G.edgeFinset.card ≤ (retainedEdges G S ∪ S.biUnion (fun v => G.incidenceFinset v)).card :=
      Finset.card_le_of_subset hcover
    _ ≤ (retainedEdges G S).card + (S.biUnion (fun v => G.incidenceFinset v)).card :=
      Finset.card_union_le _ _
    _ ≤ (retainedEdges G S).card + S.card*(N-1) := Nat.add_le_add_left hdeleted _

theorem edge_card_le_retained_add_five (S : Finset (Fin N)) (hS : S.card = 5) :
    G.edgeFinset.card ≤ (retainedEdges G S).card + 5*(N-1) := by
  simpa only [hS] using edge_card_le_retained_add G S

variable {R : Type*} [Fintype R] [DecidableEq R]

private theorem map_mem_edgeFinset_comap (e : R ↪ Fin N) (z : Sym2 R) :
    Sym2.map e z ∈ G.edgeFinset ↔ z ∈ (G.comap e).edgeFinset := by
  induction' z using Sym2.ind with a b
  simp only [Sym2.map_pair_eq,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
    SimpleGraph.comap_adj]

/-- The retained edges are exactly the injective image of the edges of
the actual graph pulled back to any enumeration of the surviving vertices. -/
theorem image_comap_edgeFinset_eq_retained (S : Finset (Fin N)) (e : R ↪ Fin N)
    (hRange : ∀ v, (∃ i, e i = v) ↔ v ∉ S) :
    (G.comap e).edgeFinset.image (Sym2.map e) = retainedEdges G S := by
  classical
  apply Finset.ext
  intro z
  constructor
  · intro hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    rw [mem_retainedEdges]
    refine ⟨(map_mem_edgeFinset_comap G e w).mpr hw,?_⟩
    intro v hv
    obtain ⟨i,_,he⟩ := Sym2.mem_map.mp hv
    exact (hRange v).mp ⟨i,he⟩
  · intro hz
    rw [mem_retainedEdges] at hz
    induction' z using Sym2.ind with a b
    have ha : a ∉ S := hz.2 a (Sym2.mem_mk''_left a b)
    have hb : b ∉ S := hz.2 b (Sym2.mem_mk''_right a b)
    obtain ⟨a',ha'⟩ := (hRange a).mpr ha
    obtain ⟨b',hb'⟩ := (hRange b).mpr hb
    apply Finset.mem_image.mpr
    refine ⟨(⟦(a',b')⟧ : Sym2 R),?_,?_⟩
    · apply (map_mem_edgeFinset_comap G e _).mp
      simpa only [Sym2.map_pair_eq,ha',hb'] using hz.1
    · simp only [Sym2.map_pair_eq,ha',hb']

/-- This is an equality with the actual relabeled induced graph's count,
not a new reduced predicate standing in for that graph. -/
theorem comap_edge_card_eq_retained (S : Finset (Fin N)) (e : R ↪ Fin N)
    (hRange : ∀ v, (∃ i, e i = v) ↔ v ∉ S) :
    (G.comap e).edgeFinset.card = (retainedEdges G S).card := by
  classical
  calc
    (G.comap e).edgeFinset.card = ((G.comap e).edgeFinset.image (Sym2.map e)).card :=
      (Finset.card_image_of_injective _ (Sym2.map.injective e.injective)).symm
    _ = (retainedEdges G S).card := congrArg Finset.card
      (image_comap_edgeFinset_eq_retained G S e hRange)

theorem edge_card_le_comap_add (S : Finset (Fin N)) (e : R ↪ Fin N)
    (hRange : ∀ v, (∃ i, e i = v) ↔ v ∉ S) :
    G.edgeFinset.card ≤ (G.comap e).edgeFinset.card + S.card*(N-1) := by
  rw [comap_edge_card_eq_retained G S e hRange]
  exact edge_card_le_retained_add G S

theorem edge_card_le_comap_add_five (S : Finset (Fin N)) (hS : S.card = 5)
    (e : R ↪ Fin N) (hRange : ∀ v, (∃ i, e i = v) ↔ v ∉ S) :
    G.edgeFinset.card ≤ (G.comap e).edgeFinset.card + 5*(N-1) := by
  simpa only [hS] using edge_card_le_comap_add G S e hRange

/-- The ordinary subtype-based induced graph is a special case of the
same exact retained-edge correspondence. -/
theorem induce_edge_card_eq_retained (S : Finset (Fin N)) :
    (G.induce ((S : Set (Fin N))ᶜ)).edgeFinset.card = (retainedEdges G S).card := by
  classical
  apply comap_edge_card_eq_retained G S (Function.Embedding.subtype _)
  intro v
  constructor
  · rintro ⟨i,rfl⟩
    exact i.property
  · intro hv
    exact ⟨⟨v,hv⟩,rfl⟩

/-- The concrete five-vertex deletion inequality in the real form used by
the actual weighted counting theorem, with m surviving vertices. -/
theorem five_vertex_deletion_lower_bound {m : ℕ} (H : SimpleGraph (Fin (m+5)))
    [DecidableRel H.Adj] (S : Finset (Fin (m+5))) (hS : S.card = 5)
    (e : Fin m ↪ Fin (m+5)) (hRange : ∀ v, (∃ i, e i = v) ↔ v ∉ S) :
    (H.edgeFinset.card : ℝ)-5*((m : ℝ)+4) ≤ ((H.comap e).edgeFinset.card : ℝ) := by
  have hnat := edge_card_le_comap_add_five H S hS e hRange
  have hN : m+5-1=m+4 := Nat.add_sub_assoc (by decide : 1≤5) m
  have hnat' : H.edgeFinset.card ≤ (H.comap e).edgeFinset.card + 5*(m+4) := by
    simpa only [hN] using hnat
  have hr : (H.edgeFinset.card : ℝ) ≤ ((H.comap e).edgeFinset.card : ℝ)+5*((m : ℝ)+4) := by
    exact_mod_cast hnat'
  linarith only [hr]

#print axioms edge_card_le_retained_add
#print axioms image_comap_edgeFinset_eq_retained
#print axioms comap_edge_card_eq_retained
#print axioms induce_edge_card_eq_retained
#print axioms five_vertex_deletion_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
