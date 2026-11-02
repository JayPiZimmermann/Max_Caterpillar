import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Identity
import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Damage
import MaxCaterpillar.Frontier.RandomRestriction.CoinRankSizeBias

/-! # A size-bias bound for the actual partial-matching edge count

The random object in the conclusion is an ordinary uniform vertex permutation.
The coupling identity and its three-pair damage bound are proved from the two
actual position transpositions, rather than supplied as assumptions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
open BigOperators

variable {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

theorem matchingMean_eq_edges (K : ℕ) : matchingMean G K =
    2*(K : ℝ)*(G.edgeFinset.card : ℝ)/((m : ℝ)*((m : ℝ)-1)) := by
  unfold matchingMean
  rw [oriented_edge_card]
  push_cast
  ring

/-- All three standard coupling conditions are derived for the actual joint
experiment, with its uniform-permutation first marginal. -/
theorem actual_matching_size_bias_coupling (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K)
    (hE : 0<Fintype.card (OrientedEdge G)) :
    (∑ ω : CouplingSample G K,uniformWeight G ω)=1 ∧
      FiniteSizeBiasIdentity (uniformWeight G) (sampleCount G P)
        (sampleCoupledCount G P) (matchingMean G K) ∧
      (∀ ω : CouplingSample G K,sampleCoupledCount G P ω≤sampleCount G P ω+3) :=
  ⟨uniformWeight_sum G hK hE,finite_size_bias_identity G P hP hE,
    sampleCoupledCount_le G P hP⟩

/-- Uniform permutations of all vertices satisfy the geometric-moment bound
for every fixed collection of disjoint selected position pairs. -/
theorem matching_geometric_le (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K)
    (hE : 0<Fintype.card (OrientedEdge G)) (θ : ℝ)
    (hθ : 0<θ) (hθone : θ≤1) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),θ^(matchingCount G P τ)) ≤
      Real.exp (-(matchingMean G K)*(1-θ^3)/3) := by
  have hsize := finite_size_bias_identity G P hP hE
  have hbound := finite_geometric_le_of_size_bias_three (uniformWeight G)
    (fun ω : CouplingSample G K => matchingCount G P ω.1)
    (sampleCoupledCount G P) (matchingMean G K) θ
    (uniformWeight_nonneg G) (uniformWeight_sum G hK hE)
    (matchingMean_nonneg G hE) hsize (sampleCoupledCount_le G P hP) hθ hθone
  have hmarginal := uniform_permutation_marginal G hK hE
    (fun τ => θ^(matchingCount G P τ))
  exact hmarginal.symm.trans_le hbound

/-- The mean is written in terms of the number of ordinary undirected graph
edges. All hypotheses concern the actual graph and selected positions. -/
theorem matching_geometric_le_edges (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K) (hG : 0<G.edgeFinset.card)
    (θ : ℝ) (hθ : 0<θ) (hθone : θ≤1) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),θ^(matchingCount G P τ)) ≤
      Real.exp (-(2*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1)))*(1-θ^3)/3) := by
  have hE : 0<Fintype.card (OrientedEdge G) := by
    rw [oriented_edge_card]
    exact Nat.mul_pos (by decide) hG
  simpa only [matchingMean_eq_edges] using
    matching_geometric_le G P hP hK hE θ hθ hθone

/-- At theta=1/2 the exact exponential rate is 7K|E|/(12m(m-1)). -/
theorem matching_half_moment_le (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K) (hG : 0<G.edgeFinset.card) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ)) ≤
      Real.exp (-(7/12 : ℝ)*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1))) := by
  calc
    _ ≤ Real.exp (-(2*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1)))*(1-(1/2 : ℝ)^3)/3) :=
      matching_geometric_le_edges G P hP hK hG (1/2) (by norm_num) (by norm_num)
    _ = _ := by
      congr 1
      norm_num
      ring

#check @matching_geometric_le_edges
#print axioms actual_matching_size_bias_coupling
#print axioms matching_geometric_le_edges
#print axioms matching_half_moment_le
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
