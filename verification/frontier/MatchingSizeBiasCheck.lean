import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias

set_option autoImplicit false
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias

-- The conclusion concerns the ordinary uniform permutation, not a
-- replacement probability model with a postulated size-bias identity.
example {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (hK : 0<K) (hG : 0<G.edgeFinset.card)
    (θ : ℝ) (hθ : 0<θ) (hθone : θ≤1) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),θ^(matchingCount G P τ)) ≤
      Real.exp (-(2*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1)))*(1-θ^3)/3) :=
  matching_geometric_le_edges G P hP hK hG θ hθ hθone

example {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (hK : 0<K) (hG : 0<G.edgeFinset.card) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ)) ≤
      Real.exp (-(7/12 : ℝ)*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1))) :=
  matching_half_moment_le G P hP hK hG

example {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P) (hK : 0<K)
    (hE : 0<Fintype.card (OrientedEdge G)) :
    (∑ ω : CouplingSample G K,uniformWeight G ω)=1 ∧
      FiniteSizeBiasIdentity (uniformWeight G) (sampleCount G P)
        (sampleCoupledCount G P) (matchingMean G K) ∧
      (∀ ω : CouplingSample G K,sampleCoupledCount G P ω≤sampleCount G P ω+3) :=
  actual_matching_size_bias_coupling G P hP hK hE

example {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (τ : Equiv.Perm (Fin m)) (i : Fin K) (a b : Fin m) :
    matchingCount G P (forcePair τ (P (i,0)) (P (i,1)) a b) ≤
      matchingCount G P τ+3 := matchingCount_forcePair_le G P hP τ i a b

-- The constant400 applies to the displayed weighted expression, retaining
-- the genuine graph edge-deletion and selected-pair hypotheses.
example {m J : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin J × Fin 2 → Fin m) (hP : Function.Injective P)
    (hG : 0<G.edgeFinset.card) (K η : ℝ)
    (hm : 400≤(m : ℝ)) (hK : 0<K) (hKcut : K≤(m : ℝ)/100)
    (hη : 0≤η) (hJ : K/2≤(J : ℝ))
    (hE : η-5*((m : ℝ)+4)≤(G.edgeFinset.card : ℝ)) :
    60*η^2/(m : ℝ)^4 *
        ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
          (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ))) ≤
      400/K^2 :=
  actual_matching_counting_le_four_hundred G P hP hG K η hm hK hKcut hη hJ hE

#check @forcingEquiv
#check @forcing_preimage_card
#print axioms forcingEquiv
#print axioms forcing_preimage_card
#print axioms forcePair_apply_away
#print axioms oriented_edge_card
#print axioms uniform_permutation_marginal
#print axioms finite_size_bias_identity
#print axioms matchingCount_forcePair_le
#print axioms sampleCoupledCount_le
#print axioms actual_matching_size_bias_coupling
#print axioms matching_geometric_le
#print axioms matching_geometric_le_edges
#print axioms matching_half_moment_le
#print axioms actual_matching_counting_le_four_hundred
