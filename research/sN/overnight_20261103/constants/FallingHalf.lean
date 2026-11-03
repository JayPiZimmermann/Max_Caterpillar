import MaxCaterpillar.Frontier.RandomRestriction.WeightedRestriction

/-! A sharper support restriction uses the fourth falling factorial actually
charged by the interference bound, rather than the fourth power. -/
set_option autoImplicit false
namespace MaxCaterpillar.Overnight.Constants.FallingHalf
open BigOperators WeightedRestriction

/-- The sharp dyadic envelope is attained at support sizes seven and eight. -/
theorem falling_four_decay (s : ℕ) : 16 * s.descFactorial 4 ≤ 105 * 2 ^ s := by
  have step (s : ℕ) (hs : 7 ≤ s) :
      (s+1).descFactorial 4 ≤ 2*s.descFactorial 4 := by
    have hsub : s-3+3=s := Nat.sub_add_cancel ((by decide : 3≤7).trans hs)
    have hc : s+1 ≤ 2*(s-3) := by linarith only [hs, hsub]
    have hh := Nat.mul_le_mul_right (s.descFactorial 3) hc
    simpa only [Nat.succ_descFactorial_succ, Nat.descFactorial_succ,
      Nat.mul_assoc] using hh
  have core : ∀ s : ℕ, 7 ≤ s → 16*s.descFactorial 4 ≤ 105*2^s := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => norm_num [Nat.descFactorial]
    | succ s hs ih =>
      have hh := step s hs
      rw [Nat.pow_succ 2 s]
      linarith only [ih, hh]
  by_cases hs : s < 7
  · interval_cases s <;> norm_num [Nat.descFactorial]
  · exact core s (Nat.le_of_not_gt hs)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

/-- Generic selector averaging, for any nonnegative integer support charge
with an exponential envelope. This also handles empty supports correctly. -/
theorem exists_selector_cost (T : κ → Finset (ι × Bool)) (cost : ℕ → ℕ)
    (a b : ℕ) (hdecay : ∀ s, a*cost s ≤ b*2^s) :
    ∃ f : ι → Bool,
      a*(∑ j, if f ∈ containing (T j) then cost (T j).card else 0) ≤
        b*Fintype.card κ := by
  classical
  have one (j : κ) :
      a*(∑ f : ι → Bool, if f ∈ containing (T j) then cost (T j).card else 0)
        ≤ b*2^Fintype.card ι := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    calc
      a*((containing (T j)).card*cost (T j).card) =
          (a*cost (T j).card)*(containing (T j)).card := by ring
      _ ≤ (b*2^(T j).card)*(containing (T j)).card :=
        Nat.mul_le_mul_right _ (hdecay (T j).card)
      _ = b*((containing (T j)).card*2^(T j).card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left b (containing_card_bound (T j))
  have total :
      (∑ f : ι → Bool,
        a*(∑ j, if f ∈ containing (T j) then cost (T j).card else 0)) ≤
      ∑ _f : ι → Bool, b*Fintype.card κ := by
    calc
      _ = ∑ j : κ,
          a*(∑ f : ι → Bool, if f ∈ containing (T j) then cost (T j).card else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ _j : κ, b*2^Fintype.card ι := Finset.sum_le_sum fun j _ => one j
      _ = _ := by
        have hc : Fintype.card (ι → Bool)=2^Fintype.card ι := by
          simp only [Fintype.card_pi, Fintype.card_bool,
            Finset.prod_const, Finset.card_univ]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hc, Nat.cast_id]
        ring
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty total
  exact ⟨f, hf⟩

theorem paired_falling_restriction (T : κ → Finset (ι × Bool)) :
    ∃ U : Finset (ι × Bool), U.card=Fintype.card ι ∧
      16*(∑ j, if T j ⊆ U then (T j).card.descFactorial 4 else 0) ≤
        105*Fintype.card κ := by
  classical
  obtain ⟨f, hf⟩ := exists_selector_cost T (fun s => s.descFactorial 4) 16 105 falling_four_decay
  exact ⟨selected f, selected_card f, by simpa only [subset_selected] using hf⟩

theorem half_falling_restriction {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hα : Fintype.card α=2*n) (T : κ → Finset α) :
    ∃ U : Finset α, U.card=n ∧
      16*(∑ j, if T j ⊆ U then (T j).card.descFactorial 4 else 0) ≤
        105*Fintype.card κ := by
  classical
  let e : (Fin n × Bool) ≃ α := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hα]
    exact Nat.mul_comm n 2)
  let Q : κ → Finset (Fin n × Bool) := fun j => (T j).map e.symm.toEmbedding
  obtain ⟨U, hcard, hmoment⟩ := paired_falling_restriction Q
  refine ⟨U.map e.toEmbedding, ?_, ?_⟩
  · simpa only [Finset.card_map, Fintype.card_fin] using hcard
  · have hsub : ∀ j, Q j ⊆ U ↔ T j ⊆ U.map e.toEmbedding := by
      intro j
      rw [← Finset.map_subset_map (f:=e.toEmbedding)]
      simp [Q, Finset.map_map]
    simpa only [Q, Finset.card_map, hsub] using hmoment

#check @falling_four_decay
#check @half_falling_restriction
#print axioms falling_four_decay
#print axioms half_falling_restriction
end MaxCaterpillar.Overnight.Constants.FallingHalf
