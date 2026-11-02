import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # The actual event of two disjoint graph edges in the five selected labels

Ordinary edges are unordered `Sym2` values in the graph's real edge finset.
The finite union cover is proved from the literal existential event.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
open BigOperators

noncomputable def edgeVertices {N : ℕ} (e : Sym2 (Fin N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun v => v∈e

@[simp] theorem mem_edgeVertices {N : ℕ} (e : Sym2 (Fin N)) (v : Fin N) :
    v∈edgeVertices e ↔ v∈e := by
  classical
  simp [edgeVertices]

theorem edgeVertices_mk {N : ℕ} (a b : Fin N) :
    edgeVertices (⟦(a,b)⟧ : Sym2 (Fin N)) = {a,b} := by
  classical
  ext v
  simp [Sym2.mem_iff']

theorem edgeVertices_card {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (e : Sym2 (Fin N)) (he : e∈G.edgeFinset) :
    (edgeVertices e).card=2 := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      have hab : a≠b := ((SimpleGraph.mem_edgeSet G).mp
        (SimpleGraph.mem_edgeFinset.mp he)).ne
      rw [edgeVertices_mk]
      simp [hab]

def hasTwoDisjointSelectedEdges {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N)) : Prop :=
  ∃ e∈G.edgeFinset,∃ f∈G.edgeFinset,e≠f ∧
    Disjoint (edgeVertices e) (edgeVertices f) ∧
      edgeVertices e∪edgeVertices f ⊆ GoodEvent.smallRankGaps τ 5

noncomputable def twoEdgesEvent {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : Finset (Equiv.Perm (Fin N)) := by
  classical
  exact Finset.univ.filter (hasTwoDisjointSelectedEdges G)

@[simp] theorem mem_twoEdgesEvent {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N)) :
    τ∈twoEdgesEvent G ↔ hasTwoDisjointSelectedEdges G τ := by
  classical
  simp [twoEdgesEvent]

noncomputable def disjointEdgePairs {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : Finset (Finset (Sym2 (Fin N))) := by
  classical
  exact (G.edgeFinset.powersetCard 2).filter fun B =>
    ∀ e∈B,∀ f∈B,e≠f → Disjoint (edgeVertices e) (edgeVertices f)

noncomputable def pairVertices {N : ℕ} (B : Finset (Sym2 (Fin N))) : Finset (Fin N) := by
  classical
  exact B.biUnion edgeVertices

theorem pairVertices_pair {N : ℕ} (e f : Sym2 (Fin N)) :
    pairVertices {e,f}=edgeVertices e∪edgeVertices f := by
  classical
  simp [pairVertices]

theorem mem_disjointEdgePairs_iff {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (B : Finset (Sym2 (Fin N))) :
    B∈disjointEdgePairs G ↔ B⊆G.edgeFinset ∧ B.card=2 ∧
      ∀ e∈B,∀ f∈B,e≠f → Disjoint (edgeVertices e) (edgeVertices f) := by
  classical
  simp only [disjointEdgePairs,Finset.mem_filter,Finset.mem_powersetCard]
  tauto

theorem pair_mem_disjointEdgePairs {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (e f : Sym2 (Fin N)) (he : e∈G.edgeFinset)
    (hf : f∈G.edgeFinset) (hef : e≠f) (hd : Disjoint (edgeVertices e) (edgeVertices f)) :
    {e,f}∈disjointEdgePairs G := by
  classical
  apply (mem_disjointEdgePairs_iff G {e,f}).mpr
  refine ⟨?_,by simp [hef],?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · simpa [h] using he
    · have hxf := Finset.mem_singleton.mp h
      simpa only [hxf] using hf
  · intro x hx y hy hxy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact hd
    · exact hd.symm
    · exact False.elim (hxy rfl)

theorem pairVertices_card {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (B : Finset (Sym2 (Fin N))) (hB : B∈disjointEdgePairs G) :
    (pairVertices B).card=4 := by
  classical
  obtain ⟨hsub,hcard,hdisj⟩ := (mem_disjointEdgePairs_iff G B).mp hB
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hcard
  have he : e∈({e,f} : Finset (Sym2 (Fin N))) := by simp
  have hf : f∈({e,f} : Finset (Sym2 (Fin N))) := by simp
  rw [pairVertices_pair,Finset.card_union_eq (hdisj e he f hf hef),
    edgeVertices_card G e (hsub he),edgeVertices_card G f (hsub hf)]

theorem disjointEdgePairs_card_le {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] :
    (disjointEdgePairs G).card≤G.edgeFinset.card.choose 2 := by
  classical
  calc
    (disjointEdgePairs G).card≤(G.edgeFinset.powersetCard 2).card :=
      Finset.card_le_of_subset (Finset.filter_subset _ _)
    _ = _ := Finset.card_powersetCard 2 G.edgeFinset

theorem hasTwoDisjointSelectedEdges_cover {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N))
    (h : hasTwoDisjointSelectedEdges G τ) :
    ∃ B∈disjointEdgePairs G,pairVertices B⊆GoodEvent.smallRankGaps τ 5 := by
  obtain ⟨e,he,f,hf,hef,hd,hsel⟩ := h
  exact ⟨{e,f},pair_mem_disjointEdgePairs G e f he hf hef hd,
    by simpa only [pairVertices_pair] using hsel⟩

#print axioms pairVertices_card
#print axioms hasTwoDisjointSelectedEdges_cover
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
