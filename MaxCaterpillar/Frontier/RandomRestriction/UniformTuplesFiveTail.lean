import MaxCaterpillar.Frontier.RandomRestriction.UniformTuples
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventGeometry

/-! # Literal full-position events with five selected positions

The common sample space has m+5 positions. Positions 0,...,4 are selected;
position j+5 is tail position j (paper tail position j+1). Full placements
are actual injections of the four role labels. Each event explicitly requires
its tail geometry and its role-by-role reconstruction in these full positions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators
variable {m : ℕ}

/-- Include a tail position into the full permutation positions. -/
def tailPosition (m : ℕ) : Fin m ↪ Fin (m+5) where
  toFun i := ⟨i.val+5,Nat.add_lt_add_right i.isLt 5⟩
  inj' := by intro i j h; apply Fin.ext; exact Nat.add_right_cancel (congrArg Fin.val h)

/-- Include one of the five selected positions into the full positions. -/
def selectedPosition (m : ℕ) : Fin 5 ↪ Fin (m+5) where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt (Nat.le_add_left 5 m)⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin (m+5) => x.val) h)

@[simp] theorem tailPosition_val (i : Fin m) : (tailPosition m i).val = i.val+5 := rfl
@[simp] theorem selectedPosition_val (i : Fin 5) : (selectedPosition m i).val = i.val := rfl

/-- Recover an actual injective tail tuple from any all-tail full tuple. -/
def tailDecode {d : ℕ} (q : Fin d ↪ Fin (m+5)) (h : ∀ i, 5 ≤ (q i).val) :
    Fin d ↪ Fin m where
  toFun i := ⟨(q i).val-5,by
    have he := Nat.sub_add_cancel (h i)
    have hb := (q i).isLt
    linarith only [he,hb]⟩
  inj' := by
    intro i j hij
    apply q.injective
    apply Fin.ext
    have hh := congrArg (fun v : Fin m => v.val) hij
    change (q i).val-5 = (q j).val-5 at hh
    have hi := Nat.sub_add_cancel (h i)
    have hj := Nat.sub_add_cancel (h j)
    linarith only [hh,hi,hj]

theorem tailDecode_reconstruct {d : ℕ} (q : Fin d ↪ Fin (m+5))
    (h : ∀ i, 5 ≤ (q i).val) (i : Fin d) :
    tailPosition m (tailDecode q h i) = q i :=
  Fin.ext (Nat.sub_add_cancel (h i))

/-- The four actual full positions realizing a tail case A tuple. -/
def CaseARealizes (q : Fin 4 ↪ Fin (m+5)) (a : Fin 4 ↪ Fin m) : Prop :=
  ∀ i, q i = tailPosition m (a i)

/-- Three tail roles and one of the five selected positions. -/
def CaseBRealizes (q : Fin 4 ↪ Fin (m+5))
    (p : (Fin 3 ↪ Fin m) × Fin 5) : Prop :=
  (∀ i : Fin 3, q i.castSucc = tailPosition m (p.1 i)) ∧
    q 3 = selectedPosition m p.2

/-- Two adjacent tail roles and two distinct ordered selected positions. -/
def CaseCRealizes (q : Fin 4 ↪ Fin (m+5))
    (p : (Fin m × Fin m) × (Fin 2 ↪ Fin 5)) : Prop :=
  q 0 = tailPosition m p.1.1 ∧ q 1 = tailPosition m p.1.2 ∧
    q 2 = selectedPosition m (p.2 0) ∧ q 3 = selectedPosition m (p.2 1)

noncomputable def fullCaseA (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin (m+5)) := by
  classical
  exact Finset.univ.filter fun q => ∃ a ∈ caseAPlacements Γ, CaseARealizes q a

noncomputable def fullCaseB (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin (m+5)) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ a ∈ caseBPlacements Γ, ∃ s : Fin 5, CaseBRealizes q (a,s)

noncomputable def fullCaseC (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin (m+5)) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ p ∈ adjacentPairs Γ, ∃ s : Fin 2 ↪ Fin 5, CaseCRealizes q (p,s)

@[simp] theorem mem_fullCaseA (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5)) :
    q ∈ fullCaseA Γ ↔ ∃ a ∈ caseAPlacements Γ, CaseARealizes q a := by
  classical
  simp [fullCaseA]
@[simp] theorem mem_fullCaseB (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5)) :
    q ∈ fullCaseB Γ ↔ ∃ a ∈ caseBPlacements Γ, ∃ s : Fin 5, CaseBRealizes q (a,s) := by
  classical
  simp [fullCaseB]
@[simp] theorem mem_fullCaseC (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5)) :
    q ∈ fullCaseC Γ ↔ ∃ p ∈ adjacentPairs Γ, ∃ s : Fin 2 ↪ Fin 5, CaseCRealizes q (p,s) := by
  classical
  simp [fullCaseC]

/-- Restrict the full role tuple to roles 0,1,2. -/
def firstThree (q : Fin 4 ↪ Fin (m+5)) : Fin 3 ↪ Fin (m+5) :=
  Fin.castSuccEmb.toEmbedding.trans q

/-- Restrict the full role tuple to roles 0,1. -/
def firstTwo (q : Fin 4 ↪ Fin (m+5)) : Fin 2 ↪ Fin (m+5) :=
  (Fin.castAddEmb 2).toEmbedding.trans q

/-- Restrict the full role tuple to roles 2,3. -/
def lastTwo (q : Fin 4 ↪ Fin (m+5)) : Fin 2 ↪ Fin (m+5) :=
  (Fin.addNatEmb 2).toEmbedding.trans q

/-- Recover an actual selected-position tuple from its literal full positions. -/
def selectedDecode {d : ℕ} (q : Fin d ↪ Fin (m+5)) (h : ∀ i, (q i).val < 5) :
    Fin d ↪ Fin 5 where
  toFun i := ⟨(q i).val,h i⟩
  inj' := by
    intro i j hij
    apply q.injective
    apply Fin.ext
    exact congrArg (fun v : Fin 5 => v.val) hij

theorem selectedDecode_reconstruct {d : ℕ} (q : Fin d ↪ Fin (m+5))
    (h : ∀ i, (q i).val < 5) (i : Fin d) :
    selectedPosition m (selectedDecode q h i) = q i := Fin.ext rfl

/-- Raw full-position case A geometry implies membership in the counted event. -/
theorem mem_fullCaseA_of_tail (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5))
    (ht : ∀ i, 5 ≤ (q i).val) (hg : tailDecode q ht ∈ caseAPlacements Γ) :
    q ∈ fullCaseA Γ := by
  apply (mem_fullCaseA Γ q).mpr
  exact ⟨tailDecode q ht,hg,fun i => (tailDecode_reconstruct q ht i).symm⟩

/-- Raw full-position case B geometry implies membership in the counted event. -/
theorem mem_fullCaseB_of_tail (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5))
    (ht : ∀ i, 5 ≤ (firstThree q i).val) (hs : (q 3).val < 5)
    (hg : tailDecode (firstThree q) ht ∈ caseBPlacements Γ) : q ∈ fullCaseB Γ := by
  apply (mem_fullCaseB Γ q).mpr
  refine ⟨tailDecode (firstThree q) ht,hg,⟨(q 3).val,hs⟩,?_,?_⟩
  · intro i
    exact (tailDecode_reconstruct (firstThree q) ht i).symm
  · exact Fin.ext rfl

/-- Raw full-position case C geometry implies membership in the counted event. -/
theorem mem_fullCaseC_of_tail (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5))
    (ht : ∀ i, 5 ≤ (firstTwo q i).val) (hs : ∀ i, (lastTwo q i).val < 5)
    (hg : TailAdjacent Γ (tailDecode (firstTwo q) ht 0)
      (tailDecode (firstTwo q) ht 1)) : q ∈ fullCaseC Γ := by
  classical
  apply (mem_fullCaseC Γ q).mpr
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
theorem fullCaseA_card_le (Γ : Finset (Fin m)) :
    (fullCaseA Γ).card ≤ (caseAPlacements Γ).card := by
  classical
  apply card_le_of_reconstructs (fullCaseA Γ) (caseAPlacements Γ) CaseARealizes
  · intro q hq
    exact (mem_fullCaseA Γ q).mp hq
  · intro q q' a h h'
    apply Function.Embedding.ext
    intro i
    exact (h i).trans (h' i).symm

/-- One selected role has exactly five available positions. -/
theorem fullCaseB_card_le (Γ : Finset (Fin m)) :
    (fullCaseB Γ).card ≤ 5 * (caseBPlacements Γ).card := by
  classical
  have hc : (fullCaseB Γ).card ≤
      ((caseBPlacements Γ).product (Finset.univ : Finset (Fin 5))).card := by
    apply card_le_of_reconstructs _ _ CaseBRealizes
    · intro q hq
      obtain ⟨a,ha,s,hs⟩ := (mem_fullCaseB Γ q).mp hq
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
      change ((caseBPlacements Γ) ×ˢ (Finset.univ : Finset (Fin 5))).card = _
      rw [Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.mul_comm]

/-- Two distinct selected roles have 5·4=20 ordered available positions. -/
theorem fullCaseC_card_le (Γ : Finset (Fin m)) :
    (fullCaseC Γ).card ≤ 20 * (adjacentPairs Γ).card := by
  classical
  have hc : (fullCaseC Γ).card ≤
      ((adjacentPairs Γ).product (Finset.univ : Finset (Fin 2 ↪ Fin 5))).card := by
    apply card_le_of_reconstructs _ _ CaseCRealizes
    · intro q hq
      obtain ⟨p,hp,s,hs⟩ := (mem_fullCaseC Γ q).mp hq
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
      change ((adjacentPairs Γ) ×ˢ (Finset.univ : Finset (Fin 2 ↪ Fin 5))).card = _
      rw [Finset.card_product,Finset.card_univ,Fintype.card_embedding_eq]
      norm_num [Nat.descFactorial,Nat.mul_comm]

#print axioms fullCaseA_card_le
#print axioms fullCaseB_card_le
#print axioms fullCaseC_card_le
#print axioms tailDecode_reconstruct
end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
