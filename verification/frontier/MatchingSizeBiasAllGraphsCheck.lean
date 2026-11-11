import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.AllGraphs

set_option autoImplicit false
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias

example {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (hK : 0<K) (θ : ℝ) (hθ : 0<θ) (hθone : θ≤1) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),θ^(matchingCount G P τ)) ≤
      Real.exp (-(2*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1)))*(1-θ^3)/3) :=
  matching_geometric_le_all_graphs G P hP hK θ hθ hθone

example {m J : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin J × Fin 2 → Fin m) (hP : Function.Injective P) (K η : ℝ)
    (hm : 400≤(m : ℝ)) (hK : 0<K) (hKcut : K≤(m : ℝ)/100)
    (hη : 0≤η) (hJ : K/2≤(J : ℝ))
    (hE : η-5*((m : ℝ)+4)≤(G.edgeFinset.card : ℝ)) :
    60*η^2/(m : ℝ)^4 *
        ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
          (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ))) ≤
      400/K^2 :=
  actual_matching_counting_le_four_hundred_all_graphs G P hP K η hm hK hKcut hη hJ hE

-- The newly included boundary is a genuine disjoint selected pair.
private def onePair : Fin 1 × Fin 2 → Fin 2 := Prod.snd
private theorem onePair_injective : Function.Injective onePair := by
  intro a b hab
  exact Prod.ext (Subsingleton.elim _ _) hab

private theorem emptyGraph_edge_card (I : Fintype (⊥ : SimpleGraph (Fin 2)).edgeSet) :
    (@SimpleGraph.edgeFinset (Fin 2) ⊥ I).card=0 := by
  have hI : I=SimpleGraph.fintypeEdgeSetBot := Subsingleton.elim _ _
  cases hI
  rw [SimpleGraph.edgeFinset_bot]
  rfl

example (τ : Equiv.Perm (Fin 2)) :
    matchingCount (⊥ : SimpleGraph (Fin 2)) onePair τ=0 :=
  matchingCount_eq_zero_of_edge_card_zero (⊥ : SimpleGraph (Fin 2))
    (emptyGraph_edge_card (SimpleGraph.fintypeEdgeSet (⊥ : SimpleGraph (Fin 2)))) onePair τ

example (θ : ℝ) :
    (Fintype.card (Equiv.Perm (Fin 2)) : ℝ)⁻¹ *
      (∑ τ : Equiv.Perm (Fin 2),θ^(matchingCount (⊥ : SimpleGraph (Fin 2)) onePair τ))=1 :=
  matching_moment_eq_one_of_edge_card_zero (⊥ : SimpleGraph (Fin 2))
    (emptyGraph_edge_card (SimpleGraph.fintypeEdgeSet (⊥ : SimpleGraph (Fin 2)))) onePair θ

#print axioms matchingCount_eq_zero_of_edge_card_zero
#print axioms matching_moment_eq_one_of_edge_card_zero
#print axioms matching_geometric_le_all_graphs
#print axioms matching_half_moment_le_all_graphs
#print axioms actual_matching_counting_le_four_hundred_all_graphs
