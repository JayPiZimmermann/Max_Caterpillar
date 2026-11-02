import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Counting

/-! # The actual matching estimates, including the zero-edge graph

When the graph is empty the original permutation count is identically zero.
No normalized size-bias experiment on an empty dart space is asserted.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
open BigOperators

variable {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

theorem matchingCount_eq_zero_of_edge_card_zero
    (hG : G.edgeFinset.card=0) (P : Fin K × Fin 2 → Fin m)
    (τ : Equiv.Perm (Fin m)) : matchingCount G P τ=0 := by
  classical
  unfold matchingCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  have hadj := (Finset.mem_filter.mp hi).2
  have hpos : 0<Fintype.card (OrientedEdge G) :=
    Fintype.card_pos_iff.mpr ⟨⟨(τ (P (i,0)),τ (P (i,1))),hadj⟩⟩
  rw [oriented_edge_card,hG,mul_zero] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- The actual uniform-permutation moment is one for an empty graph. -/
theorem matching_moment_eq_one_of_edge_card_zero
    (hG : G.edgeFinset.card=0) (P : Fin K × Fin 2 → Fin m) (θ : ℝ) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
      (∑ τ : Equiv.Perm (Fin m),θ^(matchingCount G P τ))=1 := by
  simp_rw [matchingCount_eq_zero_of_edge_card_zero G hG P,pow_zero]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- No nonempty-graph hypothesis is required for the moment bound. -/
theorem matching_geometric_le_all_graphs (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K) (θ : ℝ)
    (hθ : 0<θ) (hθone : θ≤1) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),θ^(matchingCount G P τ)) ≤
      Real.exp (-(2*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1)))*(1-θ^3)/3) := by
  by_cases hg : G.edgeFinset.card=0
  · rw [matching_moment_eq_one_of_edge_card_zero G hg P θ,hg]
    norm_num
  · exact matching_geometric_le_edges G P hP hK (Nat.pos_of_ne_zero hg) θ hθ hθone

theorem matching_half_moment_le_all_graphs (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K) :
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ)) ≤
      Real.exp (-(7/12 : ℝ)*(K : ℝ)*(G.edgeFinset.card : ℝ)/
        ((m : ℝ)*((m : ℝ)-1))) := by
  by_cases hg : G.edgeFinset.card=0
  · rw [matching_moment_eq_one_of_edge_card_zero G hg P (1/2),hg]
    norm_num
  · exact matching_half_moment_le G P hP hK (Nat.pos_of_ne_zero hg)

/-- The explicit weighted bound also covers an empty deletion graph. Its
edge-deletion premise then bounds eta, while the actual moment is exactly one. -/
theorem actual_matching_counting_le_four_hundred_all_graphs {J : ℕ}
    (P : Fin J × Fin 2 → Fin m) (hP : Function.Injective P) (K η : ℝ)
    (hm : 400≤(m : ℝ)) (hK : 0<K) (hKcut : K≤(m : ℝ)/100)
    (hη : 0≤η) (hJ : K/2≤(J : ℝ))
    (hE : η-5*((m : ℝ)+4)≤(G.edgeFinset.card : ℝ)) :
    60*η^2/(m : ℝ)^4 *
        ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
          (∑ τ : Equiv.Perm (Fin m),(1/2 : ℝ)^(matchingCount G P τ))) ≤
      400/K^2 := by
  by_cases hg : G.edgeFinset.card=0
  · have hd : η-5*((m : ℝ)+4)≤0 := by simpa only [hg,Nat.cast_zero] using hE
    have hc : -(7/24 : ℝ)*K≤0 := by nlinarith only [hK]
    have hexp : 0≤-(7/24 : ℝ)*K*(η-5*((m : ℝ)+4))/(m : ℝ)^2 :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos hc hd) (sq_nonneg _)
    have hone : 1≤Real.exp (-(7/24 : ℝ)*K*(η-5*((m : ℝ)+4))/(m : ℝ)^2) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hexp
    have hfactor : 0≤60*η^2/(m : ℝ)^4 := by positivity
    calc
      _ = 60*η^2/(m : ℝ)^4 := by
        rw [matching_moment_eq_one_of_edge_card_zero G hg P (1/2),mul_one]
      _ ≤ 60*η^2/(m : ℝ)^4 *
          Real.exp (-(7/24 : ℝ)*K*(η-5*((m : ℝ)+4))/(m : ℝ)^2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hfactor
      _ ≤ 400/K^2 :=
        matching_counting_expression_le_four_hundred (m : ℝ) K η hm hK hKcut hη
  · exact actual_matching_counting_le_four_hundred G P hP (Nat.pos_of_ne_zero hg)
      K η hm hK hKcut hη hJ hE

#check @matching_geometric_le_all_graphs
#check @actual_matching_counting_le_four_hundred_all_graphs
#print axioms matchingCount_eq_zero_of_edge_card_zero
#print axioms matching_geometric_le_all_graphs
#print axioms actual_matching_counting_le_four_hundred_all_graphs
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
