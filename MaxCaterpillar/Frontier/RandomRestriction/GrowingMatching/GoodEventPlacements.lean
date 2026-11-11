import MaxCaterpillar.Frontier.RandomRestriction.UniformTuples
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConfigurationsGeometry

/-! # Literal four-role good-event placements with arbitrary selected arity

The full position space is Fin(m+k). Its first k positions are selected, and
canonical tail position j has full position j+k. These events use actual
injective four-role tuples, exact tail geometry, and actual selected-position
witnesses. No bad-probability assertion or selected-five estimate is a premise.
All finite arities, including k=0, k=1 and empty tails, are permitted.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventPlacements
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
  (caseAPlacements caseBPlacements adjacentPairs TailAdjacent)
variable {k m : ℕ}

/-- Recover an actual injective tail tuple from any all-tail full tuple. -/
def tailDecode {d : ℕ} (q : Fin d ↪ Fin (m+k)) (h : ∀ i, k ≤ (q i).val) :
    Fin d ↪ Fin m where
  toFun i := ⟨(q i).val-k,by
    have he := Nat.sub_add_cancel (h i)
    have hb := (q i).isLt
    linarith only [he,hb]⟩
  inj' := by
    intro i j hij
    apply q.injective
    apply Fin.ext
    have hh := congrArg (fun v : Fin m => v.val) hij
    change (q i).val-k = (q j).val-k at hh
    have hi := Nat.sub_add_cancel (h i)
    have hj := Nat.sub_add_cancel (h j)
    linarith only [hh,hi,hj]

theorem tailDecode_reconstruct {d : ℕ} (q : Fin d ↪ Fin (m+k))
    (h : ∀ i, k ≤ (q i).val) (i : Fin d) :
    Configurations.tailPosition k m (tailDecode q h i) = q i :=
  Fin.ext (Nat.sub_add_cancel (h i))

/-- The four actual full positions realizing a tail case A tuple. -/
def CaseARealizes (q : Fin 4 ↪ Fin (m+k)) (a : Fin 4 ↪ Fin m) : Prop :=
  ∀ i, q i = Configurations.tailPosition k m (a i)

/-- Three tail roles and one of the k selected positions. -/
def CaseBRealizes (q : Fin 4 ↪ Fin (m+k))
    (p : (Fin 3 ↪ Fin m) × Fin k) : Prop :=
  (∀ i : Fin 3, q i.castSucc = Configurations.tailPosition k m (p.1 i)) ∧
    q 3 = Configurations.selectedPosition k m p.2

/-- Two adjacent tail roles and two distinct ordered selected positions. -/
def CaseCRealizes (q : Fin 4 ↪ Fin (m+k))
    (p : (Fin m × Fin m) × (Fin 2 ↪ Fin k)) : Prop :=
  q 0 = Configurations.tailPosition k m p.1.1 ∧ q 1 = Configurations.tailPosition k m p.1.2 ∧
    q 2 = Configurations.selectedPosition k m (p.2 0) ∧ q 3 = Configurations.selectedPosition k m (p.2 1)

noncomputable def fullCaseA (k : ℕ) (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin (m+k)) := by
  classical
  exact Finset.univ.filter fun q => ∃ a ∈ caseAPlacements Γ, CaseARealizes q a

noncomputable def fullCaseB (k : ℕ) (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin (m+k)) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ a ∈ caseBPlacements Γ, ∃ s : Fin k, CaseBRealizes q (a,s)

noncomputable def fullCaseC (k : ℕ) (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin (m+k)) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ p ∈ adjacentPairs Γ, ∃ s : Fin 2 ↪ Fin k, CaseCRealizes q (p,s)

@[simp] theorem mem_fullCaseA (k : ℕ) (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+k)) :
    q ∈ fullCaseA k Γ ↔ ∃ a ∈ caseAPlacements Γ, CaseARealizes q a := by
  classical
  simp [fullCaseA]
@[simp] theorem mem_fullCaseB (k : ℕ) (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+k)) :
    q ∈ fullCaseB k Γ ↔ ∃ a ∈ caseBPlacements Γ, ∃ s : Fin k, CaseBRealizes q (a,s) := by
  classical
  simp [fullCaseB]
@[simp] theorem mem_fullCaseC (k : ℕ) (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+k)) :
    q ∈ fullCaseC k Γ ↔ ∃ p ∈ adjacentPairs Γ, ∃ s : Fin 2 ↪ Fin k, CaseCRealizes q (p,s) := by
  classical
  simp [fullCaseC]

/-- Restrict the full role tuple to roles 0,1,2. -/
def firstThree (q : Fin 4 ↪ Fin (m+k)) : Fin 3 ↪ Fin (m+k) :=
  Fin.castSuccEmb.toEmbedding.trans q

/-- Restrict the full role tuple to roles 0,1. -/
def firstTwo (q : Fin 4 ↪ Fin (m+k)) : Fin 2 ↪ Fin (m+k) :=
  (Fin.castAddEmb 2).toEmbedding.trans q

/-- Restrict the full role tuple to roles 2,3. -/
def lastTwo (q : Fin 4 ↪ Fin (m+k)) : Fin 2 ↪ Fin (m+k) :=
  (Fin.addNatEmb 2).toEmbedding.trans q

/-- Recover an actual selected-position tuple from its literal full positions. -/
def selectedDecode {d : ℕ} (q : Fin d ↪ Fin (m+k)) (h : ∀ i, (q i).val < k) :
    Fin d ↪ Fin k where
  toFun i := ⟨(q i).val,h i⟩
  inj' := by
    intro i j hij
    apply q.injective
    apply Fin.ext
    exact congrArg (fun v : Fin k => v.val) hij

theorem selectedDecode_reconstruct {d : ℕ} (q : Fin d ↪ Fin (m+k))
    (h : ∀ i, (q i).val < k) (i : Fin d) :
    Configurations.selectedPosition k m (selectedDecode q h i) = q i := Fin.ext rfl

/-- Raw full-position case A geometry implies membership in the counted event. -/
theorem mem_fullCaseA_of_tail (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+k))
    (ht : ∀ i, k ≤ (q i).val) (hg : tailDecode q ht ∈ caseAPlacements Γ) :
    q ∈ fullCaseA k Γ := by
  apply (mem_fullCaseA k Γ q).mpr
  exact ⟨tailDecode q ht,hg,fun i => (tailDecode_reconstruct q ht i).symm⟩

/-- Raw full-position case B geometry implies membership in the counted event. -/
theorem mem_fullCaseB_of_tail (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+k))
    (ht : ∀ i, k ≤ (firstThree q i).val) (hs : (q 3).val < k)
    (hg : tailDecode (firstThree q) ht ∈ caseBPlacements Γ) : q ∈ fullCaseB k Γ := by
  apply (mem_fullCaseB k Γ q).mpr
  refine ⟨tailDecode (firstThree q) ht,hg,⟨(q 3).val,hs⟩,?_,?_⟩
  · intro i
    exact (tailDecode_reconstruct (firstThree q) ht i).symm
  · exact Fin.ext rfl

/-- Raw full-position case C geometry implies membership in the counted event. -/
theorem mem_fullCaseC_of_tail (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+k))
    (ht : ∀ i, k ≤ (firstTwo q i).val) (hs : ∀ i, (lastTwo q i).val < k)
    (hg : TailAdjacent Γ (tailDecode (firstTwo q) ht 0)
      (tailDecode (firstTwo q) ht 1)) : q ∈ fullCaseC k Γ := by
  classical
  apply (mem_fullCaseC k Γ q).mpr
  refine ⟨(tailDecode (firstTwo q) ht 0,tailDecode (firstTwo q) ht 1),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩,
    selectedDecode (lastTwo q) hs,?_,?_,?_,?_⟩
  · exact (tailDecode_reconstruct (firstTwo q) ht 0).symm
  · exact (tailDecode_reconstruct (firstTwo q) ht 1).symm
  · exact (selectedDecode_reconstruct (lastTwo q) hs 0).symm
  · exact (selectedDecode_reconstruct (lastTwo q) hs 1).symm

private theorem card_le_of_reconstructs {α β : Type*} [Fintype α] [Fintype β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    (hmap : ∀ a ∈ A, ∃ b ∈ B, R a b)
    (hunique : ∀ a a' b, R a b → R a' b → a = a') : A.card ≤ B.card := by
  classical
  let f : {a // a ∈ A} → {b // b ∈ B} := fun a =>
    ⟨Classical.choose (hmap a.val a.property),
      (Classical.choose_spec (hmap a.val a.property)).1⟩
  have hf : ∀ a, R a.val (f a).val := fun a =>
    (Classical.choose_spec (hmap a.val a.property)).2
  have hinj : Function.Injective f := by
    intro a a' he
    apply Subtype.ext
    apply hunique a.val a'.val (f a).val (hf a)
    rw [he]
    exact hf a'
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Four tail roles cost no selected-position multiplicity. -/
theorem fullCaseA_card_le (k : ℕ) (Γ : Finset (Fin m)) :
    (fullCaseA k Γ).card ≤ (caseAPlacements Γ).card := by
  classical
  apply card_le_of_reconstructs (fullCaseA k Γ) (caseAPlacements Γ) CaseARealizes
  · intro q hq
    exact (mem_fullCaseA k Γ q).mp hq
  · intro q q' a h h'
    apply Function.Embedding.ext
    intro i
    exact (h i).trans (h' i).symm

/-- One selected role has exactly k available positions. -/
theorem fullCaseB_card_le (k : ℕ) (Γ : Finset (Fin m)) :
    (fullCaseB k Γ).card ≤ k * (caseBPlacements Γ).card := by
  classical
  have hc : (fullCaseB k Γ).card ≤
      ((caseBPlacements Γ).product (Finset.univ : Finset (Fin k))).card := by
    apply card_le_of_reconstructs _ _ CaseBRealizes
    · intro q hq
      obtain ⟨a,ha,s,hs⟩ := (mem_fullCaseB k Γ q).mp hq
      exact ⟨(a,s),Finset.mem_product.mpr ⟨ha,Finset.mem_univ _⟩,hs⟩
    · intro q q' p h h'
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact (h.1 0).trans (h'.1 0).symm
      · exact (h.1 1).trans (h'.1 1).symm
      · exact (h.1 2).trans (h'.1 2).symm
      · exact h.2.trans h'.2.symm
  calc
    _ ≤ _ := hc
    _ = _ := by
      change ((caseBPlacements Γ) ×ˢ (Finset.univ : Finset (Fin k))).card = _
      rw [Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.mul_comm]

/-- Two distinct selected roles have k·(k−1) ordered available positions. -/
theorem fullCaseC_card_le (k : ℕ) (Γ : Finset (Fin m)) :
    (fullCaseC k Γ).card ≤ k.descFactorial 2 * (adjacentPairs Γ).card := by
  classical
  have hc : (fullCaseC k Γ).card ≤
      ((adjacentPairs Γ).product (Finset.univ : Finset (Fin 2 ↪ Fin k))).card := by
    apply card_le_of_reconstructs _ _ CaseCRealizes
    · intro q hq
      obtain ⟨p,hp,s,hs⟩ := (mem_fullCaseC k Γ q).mp hq
      exact ⟨(p,s),Finset.mem_product.mpr ⟨hp,Finset.mem_univ _⟩,hs⟩
    · intro q q' p h h'
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact h.1.trans h'.1.symm
      · exact h.2.1.trans h'.2.1.symm
      · exact h.2.2.1.trans h'.2.2.1.symm
      · exact h.2.2.2.trans h'.2.2.2.symm
  calc
    _ ≤ _ := hc
    _ = _ := by
      change ((adjacentPairs Γ) ×ˢ (Finset.univ : Finset (Fin 2 ↪ Fin k))).card = _
      rw [Finset.card_product,Finset.card_univ,Fintype.card_embedding_eq]
      rw [Fintype.card_fin,Fintype.card_fin,Nat.mul_comm]

/-- The same exact selected-pair factor in multiplication notation, including
k=0 and k=1 without any extra lower-size assumption. -/
theorem fullCaseC_card_mul_le (k : ℕ) (Γ : Finset (Fin m)) :
    (fullCaseC k Γ).card ≤ (k * (k-1)) * (adjacentPairs Γ).card := by
  have h := fullCaseC_card_le k Γ
  have hf : k.descFactorial 2 = k * (k-1) := by
    rw [show (2 : ℕ) = 1+1 from rfl,Nat.descFactorial_succ,Nat.descFactorial_one,Nat.mul_comm]
  rwa [hf] at h

#print axioms fullCaseA_card_le
#print axioms fullCaseB_card_le
#print axioms fullCaseC_card_le
#print axioms tailDecode_reconstruct
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventPlacements
