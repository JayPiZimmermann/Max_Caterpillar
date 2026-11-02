import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinColumn
import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraph
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.TwoEdges.Basic

/-! # The actual ambient braid interaction graph

Edges use the sum over all original first-neuron rows having exact pair
support. Symmetry follows from their actual zero sums. Disjoint-edge witnesses
are transported to the existing unordered-edge selected event explicitly. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators NormalizedNetwork
variable {N h₁ h₂ : ℕ}

lemma braidEdgeWeight_symm (A : Fin h₁ → Point N) (W : Fin h₁ → ℝ)
    (hsum : ∀ j, ∑ i, A j i=0) (a b : Fin N) :
    braidEdgeWeight A W a b=braidEdgeWeight A W b a := by
  classical
  by_cases hab : a=b
  · subst b
    rfl
  have hrows : braidEdgeRows A a b=braidEdgeRows A b a := by
    simp only [braidEdgeRows,Finset.pair_comm a b]
  unfold braidEdgeWeight
  rw [←hrows]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hsupp : rowSupport (A j) ⊆ {a,b} := (Finset.mem_filter.mp hj).2.le
  rw [row_other_endpoint (A j) a b hab (hsum j) hsupp,abs_neg]

/-- The graph is defined from the actual ambient pair-column coefficients. -/
noncomputable def braidInteractionGraph (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) : SimpleGraph (Fin N) where
  Adj a b := a≠b ∧ braidEdgeWeight net.A (net.W k) a b≠0
  symm a b h := ⟨h.1.symm,by
    rw [←braidEdgeWeight_symm net.A (net.W k) hn.1 a b]
    exact h.2⟩
  loopless a h := h.1 rfl

@[simp] lemma braidInteractionGraph_adj (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) (a b : Fin N) :
    (braidInteractionGraph net hn k).Adj a b ↔
      a≠b ∧ braidEdgeWeight net.A (net.W k) a b≠0 := Iff.rfl

/-- Two actual graph edges on S, with no common endpoint. Edge looplessness
supplies the two within-edge inequalities; the four others are explicit. -/
def HasTwoDisjointEdgesOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ a b c d, a∈S ∧ b∈S ∧ c∈S ∧ d∈S ∧ G.Adj a b ∧ G.Adj c d ∧
    a≠c ∧ a≠d ∧ b≠c ∧ b≠d

lemma hasTwoDisjointEdgesOn_univ_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    HasTwoDisjointEdgesOn G Finset.univ ↔
      ¬MaxCaterpillar.Frontier.StarCertificate.PairwiseIntersectingEdges G := by
  classical
  simp only [HasTwoDisjointEdgesOn,
    MaxCaterpillar.Frontier.StarCertificate.PairwiseIntersectingEdges,
    Finset.mem_univ,true_and,not_forall,not_imp,not_or]

lemma hasTwoDisjointEdgesOn_induce_iff {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    HasTwoDisjointEdgesOn G S ↔
      ¬MaxCaterpillar.Frontier.StarCertificate.PairwiseIntersectingEdges (G.induce (S : Set V)) := by
  classical
  constructor
  · rintro ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hac,had,hbc,hbd⟩ H
    rcases H ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩ hab hcd with h|h|h|h
    · exact hac (congrArg Subtype.val h)
    · exact had (congrArg Subtype.val h)
    · exact hbc (congrArg Subtype.val h)
    · exact hbd (congrArg Subtype.val h)
  · intro h
    obtain ⟨a,b,c,d,_,_,_,_,hab,hcd,hac,had,hbc,hbd⟩ :=
      (hasTwoDisjointEdgesOn_univ_iff (G.induce (S : Set V))).mpr h
    refine ⟨a.val,b.val,c.val,d.val,a.property,b.property,c.property,d.property,
      hab,hcd,?_,?_,?_,?_⟩
    · exact fun he => hac (Subtype.ext he)
    · exact fun he => had (Subtype.ext he)
    · exact fun he => hbc (Subtype.ext he)
    · exact fun he => hbd (Subtype.ext he)

lemma hasTwoDisjointEdgesOn_comap_iff {V W : Type*} [DecidableEq W] (G : SimpleGraph W)
    (e : V ↪ W) (S : Finset V) :
    HasTwoDisjointEdgesOn (G.comap e) S ↔ HasTwoDisjointEdgesOn G (S.image e) := by
  classical
  constructor
  · rintro ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hac,had,hbc,hbd⟩
    refine ⟨e a,e b,e c,e d,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      Finset.mem_image.mpr ⟨b,hb,rfl⟩,Finset.mem_image.mpr ⟨c,hc,rfl⟩,
      Finset.mem_image.mpr ⟨d,hd,rfl⟩,hab,hcd,?_,?_,?_,?_⟩
    · exact fun he => hac (e.injective he)
    · exact fun he => had (e.injective he)
    · exact fun he => hbc (e.injective he)
    · exact fun he => hbd (e.injective he)
  · rintro ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hac,had,hbc,hbd⟩
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d',hd',rfl⟩ := Finset.mem_image.mp hd
    refine ⟨a',b',c',d',ha',hb',hc',hd',hab,hcd,?_,?_,?_,?_⟩
    · exact fun he => hac (congrArg e he)
    · exact fun he => had (congrArg e he)
    · exact fun he => hbc (congrArg e he)
    · exact fun he => hbd (congrArg e he)

/-- A vertex-level witness produces two genuine unordered edges in the graph's
actual finite edge set, with all four endpoints selected by the permutation. -/
theorem hasTwoDisjointSelectedEdges_of_hasTwoDisjointEdgesOn
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (σ : Equiv.Perm (Fin N))
    (h : HasTwoDisjointEdgesOn G (GoodEvent.smallRankGaps σ 5)) :
    GraphRestriction.hasTwoDisjointSelectedEdges G σ := by
  classical
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hac,had,hbc,hbd⟩ := h
  let e : Sym2 (Fin N) := ⟦(a,b)⟧
  let f : Sym2 (Fin N) := ⟦(c,d)⟧
  have he : e∈G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hab)
  have hf : f∈G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hcd)
  have hef : e≠f := by
    intro heq
    have hva : a∈GraphRestriction.edgeVertices e := by
      rw [show e=⟦(a,b)⟧ from rfl,GraphRestriction.edgeVertices_mk]
      simp
    rw [heq,show f=⟦(c,d)⟧ from rfl,GraphRestriction.edgeVertices_mk] at hva
    simp only [Finset.mem_insert,Finset.mem_singleton] at hva
    exact hva.elim hac had
  refine ⟨e,he,f,hf,hef,?_,?_⟩
  · rw [show e=⟦(a,b)⟧ from rfl,show f=⟦(c,d)⟧ from rfl,
      GraphRestriction.edgeVertices_mk,GraphRestriction.edgeVertices_mk]
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hv'
    rcases hv with rfl|rfl <;> rcases hv' with h|h
    · exact hac h
    · exact had h
    · exact hbc h
    · exact hbd h
  · rw [show e=⟦(a,b)⟧ from rfl,show f=⟦(c,d)⟧ from rfl,
      GraphRestriction.edgeVertices_mk,GraphRestriction.edgeVertices_mk]
    intro v hv
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with (rfl|rfl)|(rfl|rfl)
    · exact ha
    · exact hb
    · exact hc
    · exact hd

end MaxCaterpillar.Frontier.RandomRestriction
