import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Association

/-! Canonical lower events for Bernoulli coordinate restriction of a support family. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ} {κ : Type*} [Fintype κ]

/-- Original rows whose supports have at least three labels. -/
def largeSupports (T : κ → Finset (Fin n)) : Finset κ :=
  Finset.univ.filter fun j => 3 ≤ (T j).card

/-- No original support of size at least three is fully selected. -/
noncomputable def noInternalEvent (T : κ → Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun S => ∀ j, 3 ≤ (T j).card → ¬ T j ⊆ S

/-- The lower conditioning event combining support avoidance and a size cutoff. -/
noncomputable def admissibleSets (T : κ → Finset (Fin n)) (b : ℕ) :
    Finset (Finset (Fin n)) :=
  noInternalEvent T ∩ Finset.univ.filter fun S => S.card ≤ b

@[simp] theorem mem_largeSupports (T : κ → Finset (Fin n)) (j : κ) :
    j ∈ largeSupports T ↔ 3 ≤ (T j).card := by simp [largeSupports]

@[simp] theorem mem_noInternalEvent (T : κ → Finset (Fin n)) (S : Finset (Fin n)) :
    S ∈ noInternalEvent T ↔ ∀ j, 3 ≤ (T j).card → ¬ T j ⊆ S := by
  classical
  simp [noInternalEvent]

@[simp] theorem mem_admissibleSets (T : κ → Finset (Fin n)) (b : ℕ)
    (S : Finset (Fin n)) :
    S ∈ admissibleSets T b ↔ (∀ j, 3 ≤ (T j).card → ¬ T j ⊆ S) ∧ S.card ≤ b := by
  classical
  simp [admissibleSets]

theorem isLowerSet_noInternalEvent (T : κ → Finset (Fin n)) :
    IsLowerSet (noInternalEvent T : Set (Finset (Fin n))) := by
  intro S U hSU hU
  rw [Finset.mem_coe, mem_noInternalEvent] at hU ⊢
  intro j hj hT
  exact hU j hj (hT.trans hSU)

theorem isLowerSet_admissibleSets (T : κ → Finset (Fin n)) (b : ℕ) :
    IsLowerSet (admissibleSets T b : Set (Finset (Fin n))) := by
  intro S U hSU hU
  rw [Finset.mem_coe, mem_admissibleSets] at hU ⊢
  exact ⟨fun j hj hT => hU.1 j hj (hT.trans hSU),
    (Finset.card_mono hSU).trans hU.2⟩

@[simp] theorem empty_mem_noInternalEvent (T : κ → Finset (Fin n)) :
    ∅ ∈ noInternalEvent T := by
  rw [mem_noInternalEvent]
  intro j hj hT
  have hc := Finset.card_mono hT
  simp only [Finset.card_empty] at hc
  omega

@[simp] theorem empty_mem_admissibleSets (T : κ → Finset (Fin n)) (b : ℕ) :
    ∅ ∈ admissibleSets T b := by
  exact (mem_admissibleSets T b ∅).2 ⟨(mem_noInternalEvent T ∅).1 (empty_mem_noInternalEvent T), by simp⟩

/-- A lower restriction event containing the empty selection has positive mass for `p < 1`. -/
theorem mass_pos_of_empty_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (E : Finset (Finset (Fin n))) (hE : ∅ ∈ E) : 0 < mass p E := by
  have hw : 0 < weight p (∅ : Finset (Fin n)) := by
    rw [weight_eq_pow_card]
    simp only [Finset.card_empty, pow_zero, Nat.sub_zero, one_mul]
    exact pow_pos (sub_pos.mpr hp1) n
  have hle : weight p (∅ : Finset (Fin n)) ≤ mass p E := by
    exact Finset.single_le_sum (fun S _ => weight_nonneg hp0 hp1.le S) hE
  exact hw.trans_le hle

theorem mass_noInternalEvent_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (T : κ → Finset (Fin n)) : 0 < mass p (noInternalEvent T) :=
  mass_pos_of_empty_mem hp0 hp1 _ (empty_mem_noInternalEvent T)

theorem mass_admissibleSets_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (T : κ → Finset (Fin n)) (b : ℕ) : 0 < mass p (admissibleSets T b) :=
  mass_pos_of_empty_mem hp0 hp1 _ (empty_mem_admissibleSets T b)

/-- Overlapping or repeated supports need no independence hypothesis. -/
theorem prod_one_sub_pow_le_mass_noInternalEvent {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : κ → Finset (Fin n)) :
    (∏ j in largeSupports T, (1 - p ^ (T j).card)) ≤ mass p (noInternalEvent T) := by
  classical
  let E : κ → Finset (Finset (Fin n)) := fun j =>
    Finset.univ.filter fun S => ¬ T j ⊆ S
  have hE : ∀ j ∈ largeSupports T, IsLowerSet (E j : Set (Finset (Fin n))) := by
    intro j _ S U hSU hU
    simp only [E, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    exact fun hT => hU (hT.trans hSU)
  have heq : (Finset.univ.filter fun S : Finset (Fin n) =>
      ∀ j ∈ largeSupports T, S ∈ E j) = noInternalEvent T := by
    ext S
    simp [E]
  have h := prod_mass_le_mass_all hp0 hp1 (largeSupports T) E hE
  calc
    (∏ j in largeSupports T, (1 - p ^ (T j).card)) =
        ∏ j in largeSupports T, mass p (E j) := by
      apply Finset.prod_congr rfl
      intro j _
      exact (mass_avoids p (T j)).symm
    _ ≤ mass p (Finset.univ.filter fun S : Finset (Fin n) =>
        ∀ j ∈ largeSupports T, S ∈ E j) := by
      convert h using 2
      ext S
      simp
    _ = mass p (noInternalEvent T) := congrArg (mass p) heq

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
