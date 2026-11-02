import Mathlib.Tactic
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset

/-! Finite matching hitting moments under literal distinct-label inclusion bounds.
The distribution consists of an explicit finite sample space, nonnegative weights,
and an actual selected-label function. No moment or correlation conclusion is assumed. -/
set_option autoImplicit false
namespace MaxCaterpillar.Research.ExponentialPush20261102.Counting.MatchingMoment
open BigOperators
variable {Ω V ι : Type*} [Fintype Ω] [DecidableEq V]

/-- Literal indicator that the prescribed labels are all selected. -/
def containsIndicator (I S : Finset V) : ℝ := if I ⊆ S then 1 else 0

/-- A linear majorant of the factor contributed by one matching edge. -/
noncomputable def edgeFactor (e : (ι × Bool) ↪ V) (i : ι) (S : Finset V) : ℝ :=
  (1 / 2 : ℝ) + (1 / 2 : ℝ) *
    ((if e (i, false) ∈ S then 1 else 0) + (if e (i, true) ∈ S then 1 else 0))

theorem containsIndicator_insert (v : V) (I S : Finset V) :
    containsIndicator (insert v I) S =
      containsIndicator I S * (if v ∈ S then 1 else 0) := by
  classical
  have hsub : insert v I ⊆ S ↔ v ∈ S ∧ I ⊆ S := by
    constructor
    · intro h
      exact ⟨h (Finset.mem_insert_self v I), fun x hx => h (Finset.mem_insert_of_mem hx)⟩
    · rintro ⟨hv, hI⟩ x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact hI hx
  by_cases hI : I ⊆ S <;> by_cases hv : v ∈ S <;>
    simp [containsIndicator, hsub, hI, hv]

theorem edgeFactor_nonneg (e : (ι × Bool) ↪ V) (i : ι) (S : Finset V) :
    0 ≤ edgeFactor e i S := by
  unfold edgeFactor
  split_ifs <;> norm_num

/-- Expanding one edge creates at most one new required label per term. -/
theorem weighted_product_expansion (w : Ω → ℝ) (selected : Ω → Finset V)
    (e : (ι × Bool) ↪ V) (i : ι) (I : Finset V) (J : Finset ι) :
    (∑ ω, w ω * containsIndicator I (selected ω) *
      (edgeFactor e i (selected ω) * ∏ j in J, edgeFactor e j (selected ω))) =
    (1/2 : ℝ) * (∑ ω, w ω * containsIndicator I (selected ω) *
      ∏ j in J, edgeFactor e j (selected ω)) +
    (1/2 : ℝ) * (∑ ω, w ω * containsIndicator (insert (e (i,false)) I) (selected ω) *
      ∏ j in J, edgeFactor e j (selected ω)) +
    (1/2 : ℝ) * (∑ ω, w ω * containsIndicator (insert (e (i,true)) I) (selected ω) *
      ∏ j in J, edgeFactor e j (selected ω)) := by
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, containsIndicator_insert]
  apply Finset.sum_congr rfl
  intro ω _
  unfold edgeFactor
  ring

/-- The multiaffine moment bound, retaining an auxiliary set of required labels. -/
theorem weighted_product_le (w : Ω → ℝ) (selected : Ω → Finset V)
    (e : (ι × Bool) ↪ V) {p : ℝ}
    (hinclusion : ∀ I : Finset V,
      (∑ ω, w ω * containsIndicator I (selected ω)) ≤ p ^ I.card)
    (J : Finset ι) (I : Finset V)
    (hfree : ∀ i ∈ J, e (i,false) ∉ I ∧ e (i,true) ∉ I) :
    (∑ ω, w ω * containsIndicator I (selected ω) *
      ∏ i in J, edgeFactor e i (selected ω)) ≤
      p ^ I.card * (1/2 + p) ^ J.card := by
  classical
  induction J using Finset.induction_on generalizing I with
  | empty => simpa using hinclusion I
  | @insert i J hi ih =>
    have hI : e (i,false) ∉ I ∧ e (i,true) ∉ I :=
      hfree i (Finset.mem_insert_self i J)
    have hfreeJ : ∀ j ∈ J, e (j,false) ∉ I ∧ e (j,true) ∉ I :=
      fun j hj => hfree j (Finset.mem_insert_of_mem hj)
    have hdistinct (j : ι) (hj : j ∈ J) (s t : Bool) : e (j,s) ≠ e (i,t) := by
      intro heq
      have hji : j = i := congrArg Prod.fst (e.injective heq)
      exact hi (hji ▸ hj)
    have hfreeL : ∀ j ∈ J,
        e (j,false) ∉ insert (e (i,false)) I ∧ e (j,true) ∉ insert (e (i,false)) I := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      exact ⟨⟨hdistinct j hj false false, (hfreeJ j hj).1⟩,
        ⟨hdistinct j hj true false, (hfreeJ j hj).2⟩⟩
    have hfreeR : ∀ j ∈ J,
        e (j,false) ∉ insert (e (i,true)) I ∧ e (j,true) ∉ insert (e (i,true)) I := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      exact ⟨⟨hdistinct j hj false true, (hfreeJ j hj).1⟩,
        ⟨hdistinct j hj true true, (hfreeJ j hj).2⟩⟩
    have h0 := ih I hfreeJ
    have hL := ih (insert (e (i,false)) I) hfreeL
    have hR := ih (insert (e (i,true)) I) hfreeR
    rw [Finset.card_insert_of_not_mem hI.1, pow_succ] at hL
    rw [Finset.card_insert_of_not_mem hI.2, pow_succ] at hR
    simp_rw [Finset.prod_insert hi]
    rw [weighted_product_expansion, Finset.card_insert_of_not_mem hi, pow_succ]
    nlinarith only [h0, hL, hR]

/-- Number of fixed matching edges wholly outside the selected labels. -/
def outsideCount (e : (ι × Bool) ↪ V) (J : Finset ι) (S : Finset V) : ℕ :=
  (J.filter fun i => e (i,false) ∉ S ∧ e (i,true) ∉ S).card

theorem half_pow_outsideCount_le_product (e : (ι × Bool) ↪ V)
    (J : Finset ι) (S : Finset V) :
    (1/2 : ℝ) ^ outsideCount e J S ≤ ∏ i in J, edgeFactor e i S := by
  classical
  have heq : (1/2 : ℝ) ^ outsideCount e J S =
      ∏ i in J, if e (i,false) ∉ S ∧ e (i,true) ∉ S then (1/2 : ℝ) else 1 := by
    rw [Finset.prod_ite]
    simp [outsideCount]
  rw [heq]
  apply Finset.prod_le_prod
  · intro i _
    split_ifs <;> norm_num
  · intro i _
    unfold edgeFactor
    by_cases hL : e (i,false) ∈ S <;> by_cases hR : e (i,true) ∈ S <;>
      norm_num [hL, hR]

/-- Generic matching hitting moment for an explicit finite weighted distribution.
The inclusion hypothesis is the actual weighted containment law for each label set. -/
theorem weighted_matching_moment_le (w : Ω → ℝ) (selected : Ω → Finset V)
    (hw : ∀ ω, 0 ≤ w ω) (e : (ι × Bool) ↪ V) {p : ℝ}
    (hinclusion : ∀ I : Finset V,
      (∑ ω, w ω * containsIndicator I (selected ω)) ≤ p ^ I.card)
    (J : Finset ι) :
    (∑ ω, w ω * (1/2 : ℝ) ^ outsideCount e J (selected ω)) ≤
      (1/2 + p) ^ J.card := by
  classical
  calc
    _ ≤ ∑ ω, w ω * ∏ i in J, edgeFactor e i (selected ω) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (half_pow_outsideCount_le_product e J (selected ω)) (hw ω)
    _ ≤ (1/2 + p) ^ J.card := by
      have h := weighted_product_le w selected e hinclusion J ∅ (by simp)
      simpa [containsIndicator] using h

/-- A matching of exactly `q` edges, represented by its `2q` distinct endpoint labels. -/
theorem weighted_q_matching_moment_le {q : ℕ} (w : Ω → ℝ) (selected : Ω → Finset V)
    (hw : ∀ ω, 0 ≤ w ω) (e : (Fin q × Bool) ↪ V) {p : ℝ}
    (hinclusion : ∀ I : Finset V,
      (∑ ω, w ω * containsIndicator I (selected ω)) ≤ p ^ I.card) :
    (∑ ω, w ω * (1/2 : ℝ) ^ outsideCount e Finset.univ (selected ω)) ≤
      (1/2 + p) ^ q := by
  simpa using weighted_matching_moment_le w selected hw e hinclusion Finset.univ

/-- Concrete uniform selection by all ambient rank permutations. This is the literal
uniform law used by the restriction model, rather than a uniformity premise. -/
theorem uniform_permutation_matching_moment_le {n k q : ℕ}
    (hn : 0 < n) (hkn : k ≤ n) (e : (Fin q × Bool) ↪ Fin n) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
      (∑ σ : Equiv.Perm (Fin n), (1/2 : ℝ) ^
        outsideCount e Finset.univ
          (MaxCaterpillar.Frontier.RandomRestriction.GoodEvent.smallRankGaps σ k)) ≤
      (1/2 + (k : ℝ) / n) ^ q := by
  classical
  let selected := fun σ : Equiv.Perm (Fin n) =>
    MaxCaterpillar.Frontier.RandomRestriction.GoodEvent.smallRankGaps σ k
  let w := fun _ : Equiv.Perm (Fin n) => (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hw : ∀ σ, 0 ≤ w σ := by
    intro σ
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hinclusion (I : Finset (Fin n)) :
      (∑ σ, w σ * containsIndicator I (selected σ)) ≤ ((k : ℝ) / n) ^ I.card := by
    have heq : (∑ σ : Equiv.Perm (Fin n), containsIndicator I (selected σ)) =
        (MaxCaterpillar.Frontier.RandomRestriction.GoodEvent.containmentEvent k I).card := by
      simp only [containsIndicator, selected]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
    simp only [w]
    rw [← Finset.mul_sum, heq]
    simpa only [div_eq_mul_inv, mul_comm] using
      MaxCaterpillar.Frontier.RandomRestriction.GoodEvent.containment_fraction_le hn hkn I
  have h := weighted_q_matching_moment_le w selected hw e hinclusion
  simpa only [w, selected, ← Finset.mul_sum] using h

end MaxCaterpillar.Research.ExponentialPush20261102.Counting.MatchingMoment
