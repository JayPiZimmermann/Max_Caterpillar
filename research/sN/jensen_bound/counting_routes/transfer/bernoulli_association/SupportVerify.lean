import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Support
set_option autoImplicit false
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli

-- Exact expected type: mem_largeSupports
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) (j : κ) ,
    j ∈ largeSupports T ↔ 3 ≤ (T j).card := @mem_largeSupports
#check @mem_largeSupports
#print axioms mem_largeSupports

-- Exact expected type: mem_noInternalEvent
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) (S : Finset (Fin n)) ,
    S ∈ noInternalEvent T ↔ ∀ j, 3 ≤ (T j).card → ¬ T j ⊆ S := @mem_noInternalEvent
#check @mem_noInternalEvent
#print axioms mem_noInternalEvent

-- Exact expected type: mem_admissibleSets
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) (b : ℕ)
    (S : Finset (Fin n)) ,
    S ∈ admissibleSets T b ↔ (∀ j, 3 ≤ (T j).card → ¬ T j ⊆ S) ∧ S.card ≤ b := @mem_admissibleSets
#check @mem_admissibleSets
#print axioms mem_admissibleSets

-- Exact expected type: isLowerSet_noInternalEvent
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) ,
    IsLowerSet (noInternalEvent T : Set (Finset (Fin n))) := @isLowerSet_noInternalEvent
#check @isLowerSet_noInternalEvent
#print axioms isLowerSet_noInternalEvent

-- Exact expected type: isLowerSet_admissibleSets
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) (b : ℕ) ,
    IsLowerSet (admissibleSets T b : Set (Finset (Fin n))) := @isLowerSet_admissibleSets
#check @isLowerSet_admissibleSets
#print axioms isLowerSet_admissibleSets

-- Exact expected type: empty_mem_noInternalEvent
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) ,
    ∅ ∈ noInternalEvent T := @empty_mem_noInternalEvent
#check @empty_mem_noInternalEvent
#print axioms empty_mem_noInternalEvent

-- Exact expected type: empty_mem_admissibleSets
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) (b : ℕ) ,
    ∅ ∈ admissibleSets T b := @empty_mem_admissibleSets
#check @empty_mem_admissibleSets
#print axioms empty_mem_admissibleSets

-- Exact expected type: mass_pos_of_empty_mem
example : ∀ {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (E : Finset (Finset (Fin n))) (hE : ∅ ∈ E) ,  0 < mass p E := @mass_pos_of_empty_mem
#check @mass_pos_of_empty_mem
#print axioms mass_pos_of_empty_mem

-- Exact expected type: mass_noInternalEvent_pos
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (T : κ → Finset (Fin n)) ,  0 < mass p (noInternalEvent T) := @mass_noInternalEvent_pos
#check @mass_noInternalEvent_pos
#print axioms mass_noInternalEvent_pos

-- Exact expected type: mass_admissibleSets_pos
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (T : κ → Finset (Fin n)) (b : ℕ) ,  0 < mass p (admissibleSets T b) := @mass_admissibleSets_pos
#check @mass_admissibleSets_pos
#print axioms mass_admissibleSets_pos

-- Exact expected type: prod_one_sub_pow_le_mass_noInternalEvent
example : ∀ {n : ℕ} {κ : Type*} [Fintype κ] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : κ → Finset (Fin n)) ,
    (∏ j in largeSupports T, (1 - p ^ (T j).card)) ≤ mass p (noInternalEvent T) := @prod_one_sub_pow_le_mass_noInternalEvent
#check @prod_one_sub_pow_le_mass_noInternalEvent
#print axioms prod_one_sub_pow_le_mass_noInternalEvent

example {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) :
    largeSupports T = Finset.univ.filter (fun j => 3 ≤ (T j).card) := rfl
example {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) :
    noInternalEvent T = Finset.univ.filter (fun S => ∀ j, 3 ≤ (T j).card → ¬ T j ⊆ S) := by
  classical
  rfl
example {n : ℕ} {κ : Type*} [Fintype κ] (T : κ → Finset (Fin n)) (b : ℕ) :
    admissibleSets T b = noInternalEvent T ∩ Finset.univ.filter (fun S => S.card ≤ b) := rfl
#print axioms largeSupports
#print axioms noInternalEvent
#print axioms admissibleSets
