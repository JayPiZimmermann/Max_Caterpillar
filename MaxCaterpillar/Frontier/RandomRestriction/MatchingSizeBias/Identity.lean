import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Forcing
import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Model
import MaxCaterpillar.Frontier.RandomRestriction.CoinRankSizeBias

/-! # The actual finite permutation size-bias identity

Pair-event incidence is partitioned by its unique oriented graph edge. The
ordinary forcing map is averaged through its explicit conditional-fibre
equivalence; no probabilistic coupling identity is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
open BigOperators

private def edgeConditionEquiv {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (p q : Fin m) :
    {τ : Equiv.Perm (Fin m) // G.Adj (τ p) (τ q)} ≃
      (Σ e : G.Dart,
        {σ : Equiv.Perm (Fin m) // σ p=e.fst ∧ σ q=e.snd}) where
  toFun τ := ⟨⟨(τ.val p,τ.val q),τ.property⟩,⟨τ.val,rfl,rfl⟩⟩
  invFun z := ⟨z.2.val,by rw [z.2.property.1,z.2.property.2]; exact z.1.is_adj⟩
  left_inv := by intro τ; rfl
  right_inv := by
    rintro ⟨⟨⟨a,b⟩,he⟩,⟨τ,hp,hq⟩⟩
    dsimp at hp hq
    cases hp
    cases hq
    rfl

/-- The edge at two fixed permutation positions is a unique oriented edge.
This is a finite incidence identity, with an arbitrary real test function. -/
theorem pair_edge_condition_sum {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (p q : Fin m)
    (F : Equiv.Perm (Fin m) → ℝ) :
    (∑ τ : Equiv.Perm (Fin m), if G.Adj (τ p) (τ q) then F τ else 0) =
      ∑ e : G.Dart,
        ∑ σ : {σ : Equiv.Perm (Fin m) // σ p=e.fst ∧ σ q=e.snd}, F σ.val := by
  classical
  calc
    _ = ∑ τ : {τ : Equiv.Perm (Fin m) // G.Adj (τ p) (τ q)}, F τ.val := by
      apply Finset.sum_congr_set {τ : Equiv.Perm (Fin m) | G.Adj (τ p) (τ q)}
      · intro τ hτ
        exact if_pos hτ
      · intro τ hτ
        exact if_neg hτ
    _ = ∑ z : (Σ e : G.Dart,
        {σ : Equiv.Perm (Fin m) // σ p=e.fst ∧ σ q=e.snd}), F z.2.val :=
      Fintype.sum_equiv (edgeConditionEquiv G p q) _ _ (fun _ => rfl)
    _ = _ := by rw [←Finset.univ_sigma_univ,Finset.sum_sigma]

/-- Each pinned output of the ordinary forcing map has exactly the same
source multiplicity. The coefficient is computed from actual finite types. -/
theorem forcePair_sum {m : ℕ} (p q a b : Fin m) (hpq : p≠q) (hab : a≠b)
    (F : Equiv.Perm (Fin m) → ℝ) :
    (∑ τ : Equiv.Perm (Fin m), F (forcePair τ p q a b)) =
      ((m : ℝ)*((m : ℝ)-1)) *
        ∑ σ : {σ : Equiv.Perm (Fin m) // σ p=a ∧ σ q=b}, F σ.val := by
  classical
  have hm : 1≤m := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le p.val) p.isLt)
  have hc : Fintype.card {s : Fin m // s≠p}=m-1 := by
    simpa using Fintype.card_subtype_compl (fun s : Fin m => s=p)
  calc
    _ = ∑ z : {σ : Equiv.Perm (Fin m) // σ p=a ∧ σ q=b} ×
        (Fin m × {s : Fin m // s≠p}), F z.1.val :=
      Fintype.sum_equiv (forcingEquiv p q a b hpq hab) _ _
        (fun τ => (congrArg F (forcingEquiv_fst p q a b hpq hab τ)).symm)
    _ = ∑ σ : {σ : Equiv.Perm (Fin m) // σ p=a ∧ σ q=b},
        ((m : ℝ)*((m : ℝ)-1))*F σ.val := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
        nsmul_eq_mul,Fintype.card_prod,Fintype.card_fin,hc,Nat.cast_sub hm,
        Nat.cast_one,Nat.cast_mul,mul_assoc]
    _ = _ := by rw [Finset.mul_sum]

section ActualModel
variable {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

/-- Expand the actual number of successful position pairs, and partition
each success by its unique oriented edge. -/
theorem matchingCount_test_sum (P : Fin K × Fin 2 → Fin m)
    (F : Equiv.Perm (Fin m) → ℝ) :
    (∑ τ : Equiv.Perm (Fin m), (matchingCount G P τ : ℝ)*F τ) =
      ∑ i : Fin K,∑ e : OrientedEdge G,
        ∑ σ : {σ : Equiv.Perm (Fin m) //
          σ (P (i,0))=e.fst ∧ σ (P (i,1))=e.snd}, F σ.val := by
  classical
  calc
    _ = ∑ τ : Equiv.Perm (Fin m),∑ i : Fin K,
        if G.Adj (τ (P (i,0))) (τ (P (i,1))) then F τ else 0 := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [matchingCount,Finset.natCast_card_filter,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = ∑ i : Fin K,∑ τ : Equiv.Perm (Fin m),
        if G.Adj (τ (P (i,0))) (τ (P (i,1))) then F τ else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact pair_edge_condition_sum G (P (i,0)) (P (i,1)) F

/-- Summing a function of the original permutation repeats it exactly once
for each selected pair and each oriented edge. -/
theorem source_sum_multiplicity (F : Equiv.Perm (Fin m) → ℝ) :
    (∑ ω : CouplingSample G K,F ω.1) =
      ((K : ℝ)*(Fintype.card (OrientedEdge G) : ℝ)) *
        ∑ τ : Equiv.Perm (Fin m),F τ := by
  classical
  calc
    _ = ∑ τ : Equiv.Perm (Fin m),
        ((K : ℝ)*(Fintype.card (OrientedEdge G) : ℝ))*F τ := by
      simp only [CouplingSample,Fintype.sum_prod_type,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_fin,
        Nat.cast_mul,mul_assoc]
    _ = _ := by rw [Finset.mul_sum]

/-- The actual joint forcing count has the exact size-biased incidence sum.
No conditional-distribution or coupling identity is assumed. -/
theorem coupled_test_sum (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (f : ℝ → ℝ) :
    (∑ ω : CouplingSample G K,f (sampleCoupledCount G P ω)) =
      ((m : ℝ)*((m : ℝ)-1)) *
        ∑ τ : Equiv.Perm (Fin m),
          (matchingCount G P τ : ℝ)*f (matchingCount G P τ : ℝ) := by
  classical
  calc
    _ = ∑ i : Fin K,∑ e : OrientedEdge G,∑ τ : Equiv.Perm (Fin m),
        f (matchingCount G P
          (forcePair τ (P (i,0)) (P (i,1)) e.fst e.snd) : ℝ) := by
      unfold sampleCoupledCount forcedPermutation
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin K,∑ e : OrientedEdge G,
        ((m : ℝ)*((m : ℝ)-1)) *
          ∑ σ : {σ : Equiv.Perm (Fin m) //
            σ (P (i,0))=e.fst ∧ σ (P (i,1))=e.snd},
              f (matchingCount G P σ.val : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro e _
      exact forcePair_sum (P (i,0)) (P (i,1)) e.fst e.snd
        (pair_positions_ne P hP i) (oriented_edge_endpoints_ne G e)
        (fun τ => f (matchingCount G P τ : ℝ))
    _ = ((m : ℝ)*((m : ℝ)-1)) *
        ∑ i : Fin K,∑ e : OrientedEdge G,
          ∑ σ : {σ : Equiv.Perm (Fin m) //
            σ (P (i,0))=e.fst ∧ σ (P (i,1))=e.snd},
              f (matchingCount G P σ.val : ℝ) := by
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [matchingCount_test_sum G P (fun τ => f (matchingCount G P τ : ℝ))]

/-- The uniform joint experiment has the usual uniform-permutation marginal,
for every real test function on ordinary permutations. -/
theorem uniform_permutation_marginal (hK : 0<K)
    (hE : 0<Fintype.card (OrientedEdge G)) (F : Equiv.Perm (Fin m) → ℝ) :
    (∑ ω : CouplingSample G K,uniformWeight G ω*F ω.1) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        ∑ τ : Equiv.Perm (Fin m),F τ := by
  classical
  have hT : (Fintype.card (Equiv.Perm (Fin m)) : ℝ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hKr : (K : ℝ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  have hEr : (Fintype.card (OrientedEdge G) : ℝ)≠0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hE)
  calc
    _ = (Fintype.card (CouplingSample G K) : ℝ)⁻¹ *
        ∑ ω : CouplingSample G K,F ω.1 := by
      unfold uniformWeight
      rw [Finset.mul_sum]
    _ = (Fintype.card (CouplingSample G K) : ℝ)⁻¹ *
        (((K : ℝ)*(Fintype.card (OrientedEdge G) : ℝ)) *
          ∑ τ : Equiv.Perm (Fin m),F τ) := by rw [source_sum_multiplicity G F]
    _ = _ := by
      simp only [CouplingSample,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
      field_simp [hT,hKr,hEr]
      <;> ring

theorem uniformWeight_sum (hK : 0<K) (hE : 0<Fintype.card (OrientedEdge G)) :
    ∑ ω : CouplingSample G K,uniformWeight G ω=1 := by
  have hT : (Fintype.card (Equiv.Perm (Fin m)) : ℝ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh := uniform_permutation_marginal G hK hE (fun _ => 1)
  simpa only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,inv_mul_cancel hT] using hh

theorem matchingMean_denominator_pos (hE : 0<Fintype.card (OrientedEdge G)) :
    0<(m : ℝ)*((m : ℝ)-1) := by
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp hE
  have hm : 1<m := by
    have hh : 1<Fintype.card (Fin m) :=
      Fintype.one_lt_card_iff.mpr ⟨e.fst,e.snd,e.is_adj.ne⟩
    simpa using hh
  have hmr : (1 : ℝ)<m := by exact_mod_cast hm
  exact mul_pos (by linarith only [hmr]) (sub_pos.mpr hmr)

theorem matchingMean_nonneg (hE : 0<Fintype.card (OrientedEdge G)) :
    0≤matchingMean G K :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (matchingMean_denominator_pos G hE).le

theorem matchingMean_pos (hK : 0<K) (hE : 0<Fintype.card (OrientedEdge G)) :
    0<matchingMean G K := by
  exact div_pos (mul_pos (by exact_mod_cast hK) (by exact_mod_cast hE))
    (matchingMean_denominator_pos G hE)

private lemma scalar_size_bias_rearrange (w s a d : ℝ) (hd : d≠0) :
    w*(a*s) = (a/d)*(w*(d*s)) := by
  field_simp [hd]
  <;> ring

/-- The ordinary permutation forcing experiment is exactly size biased.
The graph and disjoint position pairs determine the variables; no size-bias
identity, distributional assumption, or abstract coupling is a hypothesis. -/
theorem finite_size_bias_identity (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hE : 0<Fintype.card (OrientedEdge G)) :
    FiniteSizeBiasIdentity (uniformWeight G) (sampleCount G P)
      (sampleCoupledCount G P) (matchingMean G K) := by
  classical
  intro f
  let W : ℝ := (Fintype.card (CouplingSample G K) : ℝ)⁻¹
  let S : ℝ := ∑ τ : Equiv.Perm (Fin m),
    (matchingCount G P τ : ℝ)*f (matchingCount G P τ : ℝ)
  have hleft : (∑ ω : CouplingSample G K,
      uniformWeight G ω*sampleCount G P ω*f (sampleCount G P ω)) =
      W*(((K : ℝ)*(Fintype.card (OrientedEdge G) : ℝ))*S) := by
    change (∑ ω : CouplingSample G K,
      W*(matchingCount G P ω.1 : ℝ)*f (matchingCount G P ω.1 : ℝ)) = _
    calc
      _ = W*∑ ω : CouplingSample G K,
          (matchingCount G P ω.1 : ℝ)*f (matchingCount G P ω.1 : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by
        rw [source_sum_multiplicity G (fun τ =>
          (matchingCount G P τ : ℝ)*f (matchingCount G P τ : ℝ))]
  have hright : (∑ ω : CouplingSample G K,
      uniformWeight G ω*f (sampleCoupledCount G P ω)) =
      W*(((m : ℝ)*((m : ℝ)-1))*S) := by
    change (∑ ω : CouplingSample G K,W*f (sampleCoupledCount G P ω)) = _
    rw [←Finset.mul_sum,coupled_test_sum G P hP f]
  rw [hleft,hright]
  have hd := ne_of_gt (matchingMean_denominator_pos G hE)
  exact scalar_size_bias_rearrange W S
    ((K : ℝ)*(Fintype.card (OrientedEdge G) : ℝ))
    ((m : ℝ)*((m : ℝ)-1)) hd

/-- The explicit formula is the actual mean of the uniform joint count. -/
theorem weighted_matchingCount_mean (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (hK : 0<K)
    (hE : 0<Fintype.card (OrientedEdge G)) :
    (∑ ω : CouplingSample G K,uniformWeight G ω*sampleCount G P ω)=
      matchingMean G K := by
  have hh := finite_size_bias_identity G P hP hE (fun _ => 1)
  simpa only [mul_one,uniformWeight_sum G hK hE] using hh

/-- Test functions of the count itself inherit the ordinary uniform-
permutation marginal, including geometric powers and Laplace transforms. -/
theorem sampleCount_marginal (P : Fin K × Fin 2 → Fin m) (hK : 0<K)
    (hE : 0<Fintype.card (OrientedEdge G)) (f : ℝ → ℝ) :
    (∑ ω : CouplingSample G K,uniformWeight G ω*f (sampleCount G P ω)) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        ∑ τ : Equiv.Perm (Fin m),f (matchingCount G P τ : ℝ) :=
  uniform_permutation_marginal G hK hE (fun τ => f (matchingCount G P τ : ℝ))

end ActualModel

#print axioms pair_edge_condition_sum
#print axioms forcePair_sum
#print axioms matchingCount_test_sum
#print axioms source_sum_multiplicity
#print axioms coupled_test_sum
#print axioms uniform_permutation_marginal
#print axioms uniformWeight_sum
#print axioms matchingMean_denominator_pos
#print axioms matchingMean_nonneg
#print axioms matchingMean_pos
#print axioms finite_size_bias_identity
#print axioms weighted_matchingCount_mean
#print axioms sampleCount_marginal
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
