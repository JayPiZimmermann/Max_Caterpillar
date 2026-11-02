import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Weight

/-! FKG association and domination after conditioning on a lower event. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ}

theorem mean_mul_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset (Fin n) → ℝ} (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : Monotone f) (hg : Monotone g) :
    mean p f * mean p g ≤ mean p (fun S => f S * g S) := by
  classical
  have h := fkg f g (weight p) (weight_nonneg hp0 hp1) hf0 hg0 hf hg
    (fun S T => (weight_modular p S T).le)
  have hnorm : (∑ S : Finset (Fin n), weight p S) = 1 := mass_univ p
  simpa only [mean, hnorm, one_mul] using h

theorem mean_mul_ge_antitone {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset (Fin n) → ℝ} (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : Antitone f) (hg : Antitone g) :
    mean p f * mean p g ≤ mean p (fun S => f S * g S) := by
  classical
  have h := fkg (α := OrderDual (Finset (Fin n)))
    (fun S : OrderDual (Finset (Fin n)) => f S)
    (fun S : OrderDual (Finset (Fin n)) => g S)
    (fun S : OrderDual (Finset (Fin n)) => weight p S)
    (weight_nonneg hp0 hp1) hf0 hg0
    (fun _ _ h => hf h) (fun _ _ h => hg h)
    (fun S T => ((weight_modular p S T).trans (mul_comm _ _)).le)
  have hsum (u : Finset (Fin n) → ℝ) :
      (∑ S : OrderDual (Finset (Fin n)), u S) = ∑ S : Finset (Fin n), u S := by
    apply Finset.sum_congr
    · ext S; simp
    · intro S _; rfl
  simp_rw [hsum] at h
  have hnorm : (∑ S : Finset (Fin n), weight p S) = 1 := mass_univ p
  simpa only [mean, hnorm, one_mul] using h

theorem mean_indicator (p : ℝ) (D : Finset (Finset (Fin n))) :
    mean p (fun S => if S ∈ D then 1 else 0) = mass p D := by
  classical
  simp only [mean, mul_ite, mul_one, mul_zero, mass]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem mean_mul_indicator (p : ℝ) (D : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → ℝ) :
    mean p (fun S => f S * if S ∈ D then 1 else 0) = ∑ S in D, weight p S * f S := by
  classical
  simp only [mean, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem antitone_indicator_of_isLowerSet (D : Finset (Finset (Fin n)))
    (hD : IsLowerSet (D : Set (Finset (Fin n)))) :
    Antitone (fun S => if S ∈ D then (1 : ℝ) else 0) := by
  classical
  intro S T hST
  by_cases hT : T ∈ D
  · have hS : S ∈ D := hD hST hT
    simp [hT, hS]
  · simp [hT]
    split_ifs <;> norm_num

theorem mass_mul_le_mass_inter {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D E : Finset (Finset (Fin n)))
    (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hE : IsLowerSet (E : Set (Finset (Fin n)))) :
    mass p D * mass p E ≤ mass p (D ∩ E) := by
  classical
  have h := mean_mul_ge_antitone hp0 hp1
    (fun S => show 0 ≤ (if S ∈ D then (1 : ℝ) else 0) by split_ifs <;> norm_num)
    (fun S => show 0 ≤ (if S ∈ E then (1 : ℝ) else 0) by split_ifs <;> norm_num)
    (antitone_indicator_of_isLowerSet D hD) (antitone_indicator_of_isLowerSet E hE)
  rw [mean_indicator, mean_indicator] at h
  have heq : (fun S => (if S ∈ D then (1 : ℝ) else 0) *
      (if S ∈ E then 1 else 0)) = (fun S => if S ∈ D ∩ E then 1 else 0) := by
    funext S
    by_cases h1 : S ∈ D <;> by_cases h2 : S ∈ E <;> simp [h1, h2]
  rw [heq, mean_indicator] at h
  exact h

/-- Conditioning on a positive-mass lower event decreases nonnegative increasing means. -/
theorem condMean_le_mean {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0 < mass p D) (f : Finset (Fin n) → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Monotone f) :
    condMean p D f ≤ mean p f := by
  classical
  let g : Finset (Fin n) → ℝ := fun S => if S ∈ D then 0 else 1
  have hg0 : ∀ S, 0 ≤ g S := by intro S; dsimp [g]; split_ifs <;> norm_num
  have hg : Monotone g := by
    intro S T hST
    by_cases hT : T ∈ D
    · have hS : S ∈ D := hD hST hT
      simp [g, hT, hS]
    · simp only [g, if_neg hT]
      split_ifs <;> norm_num
  have hassoc := mean_mul_ge hp0 hp1 hf0 hg0 hf hg
  have hgmean : mean p g = 1 - mass p D := by
    have hsum : mean p g + mass p D = 1 := by
      rw [← mean_indicator]
      unfold mean
      rw [← Finset.sum_add_distrib]
      have heq : (∑ S : Finset (Fin n), (weight p S * g S +
          weight p S * (if S ∈ D then 1 else 0))) = (∑ S : Finset (Fin n), weight p S) := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S ∈ D <;> simp [g, hS]
      rw [heq]
      exact mass_univ p
    linarith
  have hfgmean : mean p (fun S => f S * g S) =
      mean p f - ∑ S in D, weight p S * f S := by
    have hsum : mean p (fun S => f S * g S) +
        (∑ S in D, weight p S * f S) = mean p f := by
      rw [← mean_mul_indicator p D f]
      unfold mean
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S ∈ D <;> simp [g, hS]
    linarith
  rw [hgmean, hfgmean] at hassoc
  have hnum : (∑ S in D, weight p S * f S) ≤ mass p D * mean p f := by
    nlinarith only [hassoc]
  unfold condMean
  exact (inv_mul_le_iff hpos).2 hnum

/-- Association iterated over an arbitrary finite family of lower events. -/
theorem prod_mass_le_mass_all {ι : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Finset ι) (E : ι → Finset (Finset (Fin n)))
    (hE : ∀ j ∈ J, IsLowerSet (E j : Set (Finset (Fin n)))) :
    (∏ j in J, mass p (E j)) ≤
      mass p (Finset.univ.filter fun S : Finset (Fin n) => ∀ j ∈ J, S ∈ E j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [mass_univ]
  | @insert j J hj ih =>
    let D := Finset.univ.filter fun S : Finset (Fin n) => ∀ i ∈ J, S ∈ E i
    have hJ : ∀ i ∈ J, IsLowerSet (E i : Set (Finset (Fin n))) :=
      fun i hi => hE i (Finset.mem_insert_of_mem hi)
    have hD : IsLowerSet (D : Set (Finset (Fin n))) := by
      intro S T hST hT
      simp only [D, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact fun i hi => hJ i hi hST (hT i hi)
    have heq : (Finset.univ.filter fun S : Finset (Fin n) => ∀ i ∈ insert j J, S ∈ E i) =
        E j ∩ D := by
      ext S
      simp [D]
    rw [Finset.prod_insert hj, heq]
    exact (mul_le_mul_of_nonneg_left (ih hJ) (mass_nonneg hp0 hp1 (E j))).trans
      (mass_mul_le_mass_inter hp0 hp1 (E j) D (hE j (Finset.mem_insert_self j J)) hD)

/-- Every fixed collection of labels remains no likelier after lower-event conditioning. -/
theorem condMean_contains_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0 < mass p D) (I : Finset (Fin n)) :
    condMean p D (fun S => if I ⊆ S then 1 else 0) ≤ p ^ I.card := by
  classical
  have hf0 : ∀ S : Finset (Fin n), 0 ≤ (if I ⊆ S then (1 : ℝ) else 0) := by
    intro S; split_ifs <;> norm_num
  have hf : Monotone (fun S : Finset (Fin n) => if I ⊆ S then (1 : ℝ) else 0) := by
    intro S T hST
    by_cases hS : I ⊆ S
    · simp [hS, hS.trans hST]
    · simp only [if_neg hS]
      split_ifs <;> norm_num
  have h := condMean_le_mean hp0 hp1 D hD hpos _ hf0 hf
  have heq : (fun S : Finset (Fin n) => if I ⊆ S then (1 : ℝ) else 0) =
      (fun S => if S ∈ Finset.univ.filter (fun T : Finset (Fin n) => I ⊆ T) then 1 else 0) := by
    funext S
    simp
  rw [heq, mean_indicator, mass_contains] at h
  simpa only [← heq] using h

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
