import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! Finite Bernoulli weights on subsets of coordinate labels. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ}

def weight (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∏ i : Fin n, if i ∈ S then p else 1 - p

def mass (p : ℝ) (E : Finset (Finset (Fin n))) : ℝ := ∑ S in E, weight p S

def mean (p : ℝ) (f : Finset (Fin n) → ℝ) : ℝ := ∑ S, weight p S * f S

noncomputable def condMean (p : ℝ) (D : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → ℝ) : ℝ :=
  (mass p D)⁻¹ * ∑ S in D, weight p S * f S

theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    0 ≤ weight p S := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem weight_eq_pow_card (p : ℝ) (S : Finset (Fin n)) :
    weight p S = p ^ S.card * (1 - p) ^ (n - S.card) := by
  classical
  unfold weight
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  congr 2
  have h : (Finset.univ.filter fun i : Fin n => i ∉ S) = Finset.univ \ S := by
    ext i
    simp
  rw [h, Finset.card_sdiff (Finset.subset_univ S)]
  simp

theorem sum_prod_choice (a b : Fin n → ℝ) :
    (∑ S : Finset (Fin n), ∏ i : Fin n, if i ∈ S then a i else b i) =
      ∏ i : Fin n, (a i + b i) := by
  classical
  rw [Finset.prod_add]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_ite]
  congr 1
  · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · congr 1
    ext i
    simp

@[simp] theorem mass_univ (p : ℝ) : mass p (Finset.univ : Finset (Finset (Fin n))) = 1 := by
  unfold mass weight
  rw [sum_prod_choice]
  simp

@[simp] theorem mean_one (p : ℝ) : mean p (fun _ : Finset (Fin n) => 1) = 1 := by
  simpa [mean, mass] using (mass_univ (n := n) p)

theorem mass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Finset (Fin n))) : 0 ≤ mass p E :=
  Finset.sum_nonneg fun S _ => weight_nonneg hp0 hp1 S

theorem weight_modular (p : ℝ) (S T : Finset (Fin n)) :
    weight p S * weight p T = weight p (S ∩ T) * weight p (S ∪ T) := by
  classical
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, mul_comm]

/-- The exact probability that every label in `I` is selected. -/
theorem mass_contains (p : ℝ) (I : Finset (Fin n)) :
    mass p (Finset.univ.filter fun S : Finset (Fin n) => I ⊆ S) = p ^ I.card := by
  classical
  have hterm (S : Finset (Fin n)) :
      (∏ i : Fin n, if i ∈ S then p else if i ∈ I then 0 else 1-p) =
        if I ⊆ S then weight p S else 0 := by
    by_cases h : I ⊆ S
    · rw [if_pos h]
      unfold weight
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · simp [hi]
      · have hI : i ∉ I := fun hI => hi (h hI)
        simp [hi, hI]
    · rw [if_neg h]
      obtain ⟨i, hiI, hiS⟩ := Finset.not_subset.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hiS, hiI]
  have hsum := sum_prod_choice (fun _ : Fin n => p) (fun i => if i ∈ I then 0 else 1-p)
  simp_rw [hterm] at hsum
  have hleft : (∑ S : Finset (Fin n), if I ⊆ S then weight p S else 0) =
      mass p (Finset.univ.filter fun S : Finset (Fin n) => I ⊆ S) := by
    simp [mass, Finset.sum_filter]
  rw [hleft] at hsum
  rw [hsum]
  have hprod : (∏ i : Fin n, (p + if i ∈ I then 0 else 1-p)) =
      ∏ i : Fin n, if i ∈ I then p else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> ring
  rw [hprod, Finset.prod_ite]
  simp [Finset.filter_mem_eq_inter]

@[simp] theorem mass_empty (p : ℝ) : mass p (∅ : Finset (Finset (Fin n))) = 0 := by
  simp [mass]

theorem mass_compl (p : ℝ) (E : Finset (Finset (Fin n))) :
    mass p Eᶜ = 1 - mass p E := by
  have h : mass p E + mass p Eᶜ = 1 := by
    unfold mass
    rw [Finset.sum_add_sum_compl]
    exact mass_univ p
  linarith

theorem mass_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {D E : Finset (Finset (Fin n))} (hDE : D ⊆ E) : mass p D ≤ mass p E := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hDE (fun S _ _ => weight_nonneg hp0 hp1 S)

theorem mass_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Finset (Fin n))) : mass p E ≤ 1 := by
  simpa only [mass_univ] using mass_mono hp0 hp1 (Finset.subset_univ E)

/-- Exact mass of avoiding simultaneous selection of all labels of a support. -/
theorem mass_avoids (p : ℝ) (I : Finset (Fin n)) :
    mass p (Finset.univ.filter fun S : Finset (Fin n) => ¬ I ⊆ S) = 1 - p ^ I.card := by
  classical
  have heq : (Finset.univ.filter fun S : Finset (Fin n) => ¬ I ⊆ S) =
      (Finset.univ.filter fun S : Finset (Fin n) => I ⊆ S)ᶜ := by
    ext S
    simp
  rw [heq, mass_compl, mass_contains]

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
