import MaxCaterpillar.Frontier.RandomRestriction.WeightedRestriction

/-! Support-size-sensitive half restriction. Every support retains its own
dyadic cost, instead of replacing all costs by a uniform worst-case bound. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WeightedSupport
open BigOperators WeightedRestriction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem exists_selector_weighted (T : κ → Finset (ι × Bool))
    (cost : ℕ → ℝ) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ f : ι → Bool,
      (∑ j, if f ∈ containing (T j) then cost (T j).card else 0) ≤
        ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
  classical
  have one (j : κ) :
      (∑ f : ι → Bool, if f ∈ containing (T j) then cost (T j).card else 0) ≤
        (2 : ℝ)^Fintype.card ι * (cost (T j).card/(2 : ℝ)^(T j).card) := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    have hc : (containing (T j)).card*(2 : ℝ)^(T j).card ≤
        (2 : ℝ)^Fintype.card ι := by exact_mod_cast containing_card_bound (T j)
    have hh := mul_le_mul_of_nonneg_right hc (hnonneg (T j).card)
    rw [←mul_div_assoc]
    apply (le_div_iff (pow_pos (by norm_num : (0:ℝ)<2) _)).mpr
    convert hh using 1 <;> ring
  have total :
      (∑ f : ι → Bool, ∑ j, if f ∈ containing (T j) then cost (T j).card else 0) ≤
        ∑ _f : ι → Bool, ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
    calc
      _ = ∑ j : κ, ∑ f : ι → Bool,
          if f ∈ containing (T j) then cost (T j).card else 0 := Finset.sum_comm
      _ ≤ ∑ j : κ, (2 : ℝ)^Fintype.card ι *
          (cost (T j).card/(2 : ℝ)^(T j).card) := Finset.sum_le_sum fun j _ => one j
      _ = _ := by
        have hc : Fintype.card (ι → Bool)=2^Fintype.card ι := by
          simp only [Fintype.card_pi,Fintype.card_bool,Finset.prod_const,Finset.card_univ]
        rw [←Finset.mul_sum]
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,hc,Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨f,_,hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty total
  exact ⟨f,hf⟩

theorem paired_weighted_restriction (T : κ → Finset (ι × Bool))
    (cost : ℕ → ℝ) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ U : Finset (ι × Bool), U.card=Fintype.card ι ∧
      (∑ j, if T j ⊆ U then cost (T j).card else 0) ≤
        ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
  classical
  obtain ⟨f,hf⟩ := exists_selector_weighted T cost hnonneg
  exact ⟨selected f,selected_card f,by simpa only [subset_selected] using hf⟩

theorem half_weighted_restriction {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hα : Fintype.card α=2*n) (T : κ → Finset α)
    (cost : ℕ → ℝ) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ U : Finset α, U.card=n ∧
      (∑ j, if T j ⊆ U then cost (T j).card else 0) ≤
        ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
  classical
  let e : (Fin n × Bool) ≃ α := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,hα]
    exact Nat.mul_comm n 2)
  let Q : κ → Finset (Fin n × Bool) := fun j => (T j).map e.symm.toEmbedding
  obtain ⟨U,hcard,hmoment⟩ := paired_weighted_restriction Q cost hnonneg
  refine ⟨U.map e.toEmbedding,?_,?_⟩
  · simpa only [Finset.card_map,Fintype.card_fin] using hcard
  · have hsub : ∀ j, Q j ⊆ U ↔ T j ⊆ U.map e.toEmbedding := by
      intro j
      rw [←Finset.map_subset_map (f:=e.toEmbedding)]
      simp [Q,Finset.map_map]
    simpa only [Q,Finset.card_map,hsub] using hmoment

variable {N n : ℕ}

theorem embedded_half_weighted_restriction (e : Fin (2*n) ↪ Fin N)
    (T : κ → Finset (Fin N)) (cost : ℕ → ℝ)
    (hzero : cost 0=0) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ U : Finset (Fin N), U.card=n ∧ U ⊆ Finset.univ.image e ∧
      (∑ j, if T j ⊆ U then cost (T j).card else 0) ≤
        ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
  classical
  let V : Finset (Fin N) := Finset.univ.image e
  let Q : κ → Finset (Fin (2*n)) := fun j =>
    if T j ⊆ V then Finset.univ.filter (fun i => e i ∈ T j) else ∅
  have hdecode (j : κ) (hj : T j ⊆ V) : (Q j).image e=T j := by
    ext i
    constructor
    · intro hi
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
      simpa only [Q,if_pos hj,Finset.mem_filter,Finset.mem_univ,true_and] using ha
    · intro hi
      obtain ⟨a,_,hai⟩ := Finset.mem_image.mp (hj hi)
      refine Finset.mem_image.mpr ⟨a,?_,hai⟩
      simp only [Q,if_pos hj,Finset.mem_filter,Finset.mem_univ,true_and]
      rwa [hai]
  obtain ⟨U,hcard,hmoment⟩ :=
    half_weighted_restriction n (Fintype.card_fin (2*n)) Q cost hnonneg
  have hUV : U.image e ⊆ V := Finset.image_subset_image (Finset.subset_univ U)
  have hcardQ (j : κ) (hj : T j ⊆ V) : (Q j).card=(T j).card := by
    have hc := Finset.card_image_of_injective (Q j) e.injective
    rw [hdecode j hj] at hc
    exact hc.symm
  have hcost :
      (∑ j, if Q j ⊆ U then cost (Q j).card else 0)=
        ∑ j, if T j ⊆ U.image e then cost (T j).card else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : T j ⊆ V
    · have hs : Q j ⊆ U ↔ T j ⊆ U.image e := by
        rw [←hdecode j hj]
        exact (Finset.image_subset_image_iff e.injective).symm
      simp only [hcardQ j hj,hs]
    · have hQ : Q j=∅ := by simp only [Q,if_neg hj]
      have hout : ¬T j ⊆ U.image e := fun h => hj (h.trans hUV)
      simp [hQ,hout,hzero]
  have hbudget : (∑ j, cost (Q j).card/(2 : ℝ)^(Q j).card) ≤
      ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : T j ⊆ V
    · rw [hcardQ j hj]
    · have hQ : Q j=∅ := by simp only [Q,if_neg hj]
      simp only [hQ,Finset.card_empty,hzero,zero_div]
      exact div_nonneg (hnonneg _) (pow_nonneg (by norm_num : (0:ℝ)≤2) _)
  refine ⟨U.image e,?_,hUV,?_⟩
  · rw [Finset.card_image_of_injective U e.injective,hcard]
  · rw [←hcost]
    exact hmoment.trans hbudget

theorem exists_half_weighted_restriction (hpair : 2*n ≤ N)
    (T : κ → Finset (Fin N)) (cost : ℕ → ℝ)
    (hzero : cost 0=0) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ U : Finset (Fin N), U.card=n ∧
      (∑ j, if T j ⊆ U then cost (T j).card else 0) ≤
        ∑ j, cost (T j).card/(2 : ℝ)^(T j).card := by
  obtain ⟨U,hcard,_,hbudget⟩ := embedded_half_weighted_restriction
    (Fin.castLEEmb hpair).toEmbedding T cost hzero hnonneg
  exact ⟨U,hcard,hbudget⟩

#check @exists_half_weighted_restriction
#print axioms exists_selector_weighted
#print axioms exists_half_weighted_restriction
end MaxCaterpillar.ExponentialPush.WeightedSupport
