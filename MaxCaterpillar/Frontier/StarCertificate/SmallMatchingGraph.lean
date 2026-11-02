import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Graphs whose edges pairwise intersect

A simple graph with no pair of disjoint edges is contained in a star or in a
triangle. The vertex type need not be finite. Nonemptiness only supplies a star
center when the graph has no edges.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate

variable {V : Type*}

/-- Every two actual graph edges share an endpoint. -/
def PairwiseIntersectingEdges (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj c d → a=c ∨ a=d ∨ b=c ∨ b=d

/-- A single vertex meets every actual edge. -/
def StarContained (G : SimpleGraph V) : Prop :=
  ∃ c, ∀ a b, G.Adj a b → a=c ∨ b=c

/-- Every edge has both endpoints among three specified vertices. -/
def TriangleContained (G : SimpleGraph V) : Prop :=
  ∃ a b c, ∀ u v, G.Adj u v → u ∈ ({a,b,c} : Set V) ∧ v ∈ ({a,b,c} : Set V)

/-- If the three edges of a triangle occur, pairwise intersection forces every
other edge to have both endpoints in that triangle. -/
theorem triangleContained_of_triangle (G : SimpleGraph V)
    (H : PairwiseIntersectingEdges G) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    TriangleContained G := by
  have hab' := hab.ne
  have hac' := hac.ne
  have hbc' := hbc.ne
  have vertex (u v : V) (huv : G.Adj u v) : u ∈ ({a,b,c} : Set V) := by
    classical
    by_cases hua : u=a
    · simp only [hua,Set.mem_insert_iff,Set.mem_singleton_iff,true_or]
    by_cases hub : u=b
    · simp only [hub,Set.mem_insert_iff,Set.mem_singleton_iff,true_or,or_true]
    by_cases huc : u=c
    · simp only [huc,Set.mem_insert_iff,Set.mem_singleton_iff,true_or,or_true]
    have hvab : v=a ∨ v=b := by
      rcases H a b u v hab huv with ha | ha | hb | hb
      · exact False.elim (hua ha.symm)
      · exact Or.inl ha.symm
      · exact False.elim (hub hb.symm)
      · exact Or.inr hb.symm
    rcases hvab with hva | hvb
    · have he := H b c u v hbc huv
      rw [hva] at he
      simp only [Ne.symm hub,Ne.symm hab',Ne.symm huc,Ne.symm hac',false_or] at he
    · have he := H a c u v hac huv
      rw [hvb] at he
      simp only [Ne.symm hua,hab',Ne.symm huc,Ne.symm hbc',false_or] at he
  exact ⟨a,b,c,fun u v huv => ⟨vertex u v huv,vertex v u huv.symm⟩⟩

/-- Any pairwise-intersecting family of graph edges is contained in a star or
triangle. This theorem needs no finiteness or decidability hypothesis. -/
theorem pairwiseIntersectingEdges_star_or_triangle [Nonempty V]
    (G : SimpleGraph V) (H : PairwiseIntersectingEdges G) :
    StarContained G ∨ TriangleContained G := by
  classical
  by_cases hs : StarContained G
  · exact Or.inl hs
  right
  have avoid (k : V) : ∃ u v, G.Adj u v ∧ u≠k ∧ v≠k := by
    by_contra hn
    apply hs
    refine ⟨k,fun u v huv => ?_⟩
    by_cases hu : u=k
    · exact Or.inl hu
    right
    by_contra hv
    exact hn ⟨u,v,huv,hu,hv⟩
  obtain ⟨a,b,hab,_,_⟩ := avoid (Classical.choice (inferInstance : Nonempty V))
  have hab' := hab.ne
  obtain ⟨u,v,huv,hua,hva⟩ := avoid a
  have second : ∃ c, G.Adj b c ∧ c≠a := by
    rcases H a b u v hab huv with ha | ha | hb | hb
    · exact False.elim (hua ha.symm)
    · exact False.elim (hva ha.symm)
    · refine ⟨v,?_,hva⟩
      simpa only [← hb] using huv
    · refine ⟨u,?_,hua⟩
      simpa only [← hb] using huv.symm
  obtain ⟨c,hbc,hca⟩ := second
  obtain ⟨u,v,huv,hub,hvb⟩ := avoid b
  have first : ∃ d, G.Adj a d ∧ d≠b := by
    rcases H a b u v hab huv with ha | ha | hb | hb
    · refine ⟨v,?_,hvb⟩
      simpa only [← ha] using huv
    · refine ⟨u,?_,hub⟩
      simpa only [← ha] using huv.symm
    · exact False.elim (hub hb.symm)
    · exact False.elim (hvb hb.symm)
  obtain ⟨d,had,hdb⟩ := first
  have hcd : c=d := by
    rcases H b c a d hbc had with hba | hbd | hca' | hcd
    · exact False.elim (hab' hba.symm)
    · exact False.elim (hdb hbd.symm)
    · exact False.elim (hca hca')
    · exact hcd
  rw [← hcd] at had
  exact triangleContained_of_triangle G H hab had hbc

end MaxCaterpillar.Frontier.StarCertificate
