import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Support
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Tails
import Mathlib.Algebra.Order.Floor

/-! Explicit Bernoulli bounds for canonical support avoidance and size conditioning. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem exp_neg_two_card_mul_cube_le_mass_noInternalEvent {p : ℝ}
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1/2) (T : κ → Finset (Fin n)) :
    Real.exp (-2 * (largeSupports T).card * p^3) ≤ mass p (noInternalEvent T) := by
  classical
  have hp1 : p ≤ 1 := by linarith
  have hpow (j : κ) (hj : j ∈ largeSupports T) : p ^ (T j).card ≤ p^3 :=
    pow_le_pow_of_le_one hp0 hp1 ((mem_largeSupports T j).mp hj)
  have hsum : (∑ j in largeSupports T, p ^ (T j).card) ≤
      (largeSupports T).card * p^3 := by
    calc
      (∑ j in largeSupports T, p ^ (T j).card) ≤ ∑ _j in largeSupports T, p^3 :=
        Finset.sum_le_sum hpow
      _ = (largeSupports T).card * p^3 := by simp
  have hcube : p^3 ≤ 1/2 := by
    have h := pow_le_pow_of_le_one hp0 hp1 (show 1 ≤ 3 by omega)
    simp only [pow_one] at h
    exact h.trans hpHalf
  calc
    Real.exp (-2 * (largeSupports T).card * p^3) ≤
        Real.exp (-2 * ∑ j in largeSupports T, p ^ (T j).card) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ ∏ j in largeSupports T, (1 - p ^ (T j).card) :=
      exp_neg_two_sum_le_prod_one_sub _ _ (fun j _ => pow_nonneg hp0 _)
        (fun j hj => (hpow j hj).trans hcube)
    _ ≤ mass p (noInternalEvent T) := prod_one_sub_pow_le_mass_noInternalEvent hp0 hp1 T

theorem mass_inter_ge_sub_compl {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset (Finset (Fin n))) : mass p A - mass p Bᶜ ≤ mass p (A ∩ B) := by
  classical
  have hpart : mass p (A ∩ B) + mass p (A \ B) = mass p A := by
    exact Finset.sum_inter_add_sum_diff A B (weight p)
  have hle : mass p (A \ B) ≤ mass p Bᶜ :=
    mass_mono hp0 hp1 (by intro S hS; simpa using (Finset.mem_sdiff.mp hS).2)
  linarith

theorem mass_admissibleSets_floor_two_mean_ge {p : ℝ}
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1/2) (T : κ → Finset (Fin n)) :
    Real.exp (-2 * (largeSupports T).card * p^3) - Real.exp (-((n : ℝ)*p)/3) ≤
      mass p (admissibleSets T ⌊2*((n : ℝ)*p)⌋₊) := by
  classical
  have hp1 : p ≤ 1 := by linarith
  let B : Finset (Finset (Fin n)) := Finset.univ.filter fun S =>
    S.card ≤ ⌊2*((n : ℝ)*p)⌋₊
  have hB : Bᶜ = Finset.univ.filter fun S : Finset (Fin n) =>
      2*((n : ℝ)*p) < (S.card : ℝ) := by
    ext S
    simp only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_le]
    exact Nat.floor_lt (by positivity)
  have htail : mass p Bᶜ ≤ Real.exp (-((n : ℝ)*p)/3) := by
    rw [hB]
    exact mass_card_gt_two_mean_le p hp0 hp1
  have hpart := mass_inter_ge_sub_compl hp0 hp1 (noInternalEvent T) B
  have hlow := exp_neg_two_card_mul_cube_le_mass_noInternalEvent hp0 hpHalf T
  change _ ≤ mass p (noInternalEvent T ∩ B)
  linarith

/-- The lower cardinality tail after conditioning on any positive-mass finite event. -/
theorem condMean_card_lt_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Finset (Fin n))) (hD : 0 < mass p D) (k : ℕ)
    (hk : (k : ℝ) ≤ 3*((n : ℝ)*p)/5) :
    condMean p D (fun S => if S.card < k then 1 else 0) ≤
      Real.exp (-3*((n : ℝ)*p)/40) / mass p D := by
  classical
  have hnum : (∑ S in D, weight p S * (if S.card < k then 1 else 0)) =
      mass p (D.filter fun S => S.card < k) := by
    simp [mass, Finset.sum_filter, mul_ite]
  have hsub : (D.filter fun S => S.card < k) ⊆
      Finset.univ.filter fun S : Finset (Fin n) =>
        (S.card : ℝ) ≤ 3*((n : ℝ)*p)/5 := by
    intro S hS
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hlt : (S.card : ℝ) < k := by exact_mod_cast (Finset.mem_filter.mp hS).2
    exact hlt.le.trans hk
  have hbound := (mass_mono hp0 hp1 hsub).trans
    (mass_card_le_three_fifths_mean_le p hp0 hp1)
  unfold condMean
  rw [hnum, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_le hD.le hbound

theorem condMean_admissibleSets_card_lt_le {p : ℝ}
    (hp0 : 0 ≤ p) (hpHalf : p ≤ 1/2) (T : κ → Finset (Fin n)) (k : ℕ)
    (hk : (k : ℝ) ≤ 3*((n : ℝ)*p)/5)
    (hden : 0 < Real.exp (-2 * (largeSupports T).card * p^3) -
      Real.exp (-((n : ℝ)*p)/3)) :
    condMean p (admissibleSets T ⌊2*((n : ℝ)*p)⌋₊)
      (fun S => if S.card < k then 1 else 0) ≤
      Real.exp (-3*((n : ℝ)*p)/40) /
        (Real.exp (-2 * (largeSupports T).card * p^3) - Real.exp (-((n : ℝ)*p)/3)) := by
  have hp1 : p < 1 := by linarith
  have hD := mass_admissibleSets_pos hp0 hp1 T ⌊2*((n : ℝ)*p)⌋₊
  exact (condMean_card_lt_le hp0 hp1.le _ hD k hk).trans
    (div_le_div_of_le_left (Real.exp_pos _).le hden
      (mass_admissibleSets_floor_two_mean_ge hp0 hpHalf T))

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
