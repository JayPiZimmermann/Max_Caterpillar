import MaxCaterpillar.Frontier.RandomRestriction.GoodEventRoles
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card

/-! # One genuine four-label embedding for each unordered support role

Pair enumerations are chosen once from the actual two-element subtype. Their
order is arbitrary and contributes no factor to the finite role count. The
resulting embedding retains the exact cherry/remainder sets and B tail/selected
labels; there is no independent ordered-tuple multiplicity in the role space.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {α : Type*} [DecidableEq α]

noncomputable def pairOrder (P : Finset α) (h : P.card = 2) : Fin 2 ≃ P :=
  (Fintype.equivFinOfCardEq (show Fintype.card P = 2 by rw [Fintype.card_coe,h])).symm

noncomputable def pairEmbedding (P : Finset α) (h : P.card = 2) : Fin 2 ↪ α :=
  (pairOrder P h).toEmbedding.trans (Function.Embedding.subtype fun x => x ∈ P)

lemma pairEmbedding_mem (P : Finset α) (h : P.card = 2) (i : Fin 2) :
    pairEmbedding P h i ∈ P := ((pairOrder P h) i).property

theorem pairEmbedding_image (P : Finset α) (h : P.card = 2) :
    Finset.univ.image (pairEmbedding P h) = P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact pairEmbedding_mem P h i
  · intro hx
    refine Finset.mem_image.mpr ⟨(pairOrder P h).symm ⟨x,hx⟩,Finset.mem_univ _,?_⟩
    change ((pairOrder P h) ((pairOrder P h).symm ⟨x,hx⟩)).val = x
    rw [Equiv.apply_symm_apply]

private def fourEmbedding (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ α where
  toFun := ![a,b,c,d]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [hab,hac,had,hbc,hbd,hcd,Ne.symm hab,Ne.symm hac,Ne.symm had,
        Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]

/-- A single actual support embedding for an A/C role, with its two unordered
pairs retained as the first and last two labels. -/
noncomputable def ACRole.embedding {T : Finset α} (R : ACRole T) : Fin 4 ↪ α := by
  let p := pairEmbedding R.cherry R.cherry_card
  let q := pairEmbedding R.other R.other_card
  have hp : p 0 ≠ p 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (p.injective he)
  have hq : q 0 ≠ q 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (q.injective he)
  have hcross : ∀ i j : Fin 2, p i ≠ q j := by
    intro i j he
    exact Finset.disjoint_left.mp R.disjoint (pairEmbedding_mem _ _ i)
      (he.symm ▸ pairEmbedding_mem _ _ j)
  exact fourEmbedding (p 0) (p 1) (q 0) (q 1) hp
    (hcross 0 0) (hcross 0 1) (hcross 1 0) (hcross 1 1) hq

@[simp] theorem ACRole.embedding_zero {T : Finset α} (R : ACRole T) :
    R.embedding 0 = pairEmbedding R.cherry R.cherry_card 0 := rfl
@[simp] theorem ACRole.embedding_one {T : Finset α} (R : ACRole T) :
    R.embedding 1 = pairEmbedding R.cherry R.cherry_card 1 := rfl
@[simp] theorem ACRole.embedding_two {T : Finset α} (R : ACRole T) :
    R.embedding 2 = pairEmbedding R.other R.other_card 0 := rfl
@[simp] theorem ACRole.embedding_three {T : Finset α} (R : ACRole T) :
    R.embedding 3 = pairEmbedding R.other R.other_card 1 := rfl

/-- A single actual support embedding for a B role, retaining the actual
ordered tail and selected labels as positions 2 and 3. -/
noncomputable def BRole.embedding {T : Finset α} (R : BRole T) : Fin 4 ↪ α := by
  let p := pairEmbedding R.cherry R.cherry_card
  have hp : p 0 ≠ p 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (p.injective he)
  have ht : ∀ i : Fin 2, p i ≠ R.tail := by
    intro i he
    exact R.tail_not_mem_cherry (he ▸ pairEmbedding_mem _ _ i)
  have hs : ∀ i : Fin 2, p i ≠ R.selected := by
    intro i he
    exact R.selected_not_mem_cherry (he ▸ pairEmbedding_mem _ _ i)
  exact fourEmbedding (p 0) (p 1) R.tail R.selected hp
    (ht 0) (hs 0) (ht 1) (hs 1) R.tail_ne_selected

@[simp] theorem BRole.embedding_zero {T : Finset α} (R : BRole T) :
    R.embedding 0 = pairEmbedding R.cherry R.cherry_card 0 := rfl
@[simp] theorem BRole.embedding_one {T : Finset α} (R : BRole T) :
    R.embedding 1 = pairEmbedding R.cherry R.cherry_card 1 := rfl
@[simp] theorem BRole.embedding_two {T : Finset α} (R : BRole T) :
    R.embedding 2 = R.tail := rfl
@[simp] theorem BRole.embedding_three {T : Finset α} (R : BRole T) :
    R.embedding 3 = R.selected := rfl

/-- The first two positions enumerate exactly the original unordered cherry. -/
theorem ACRole.embedding_first_range {T : Finset α} (R : ACRole T) :
    (Finset.univ : Finset (Fin 2)).image
      (fun i => R.embedding i.castSucc.castSucc) = R.cherry := by
  have he : (fun i : Fin 2 => R.embedding i.castSucc.castSucc) =
      pairEmbedding R.cherry R.cherry_card := by
    funext i
    fin_cases i <;> rfl
  rw [he,pairEmbedding_image]

/-- The final two positions enumerate exactly the original unordered other pair. -/
theorem ACRole.embedding_last_range {T : Finset α} (R : ACRole T) :
    (Finset.univ : Finset (Fin 2)).image
      (fun i => R.embedding (i.addNat 2)) = R.other := by
  have he : (fun i : Fin 2 => R.embedding (i.addNat 2)) =
      pairEmbedding R.other R.other_card := by
    funext i
    fin_cases i <;> rfl
  rw [he,pairEmbedding_image]

theorem BRole.embedding_first_range {T : Finset α} (R : BRole T) :
    (Finset.univ : Finset (Fin 2)).image
      (fun i => R.embedding i.castSucc.castSucc) = R.cherry := by
  have he : (fun i : Fin 2 => R.embedding i.castSucc.castSucc) =
      pairEmbedding R.cherry R.cherry_card := by
    funext i
    fin_cases i <;> rfl
  rw [he,pairEmbedding_image]

theorem ACRole.embedding_mem_support {T : Finset α} (R : ACRole T) (i : Fin 4) :
    R.embedding i ∈ T := by
  fin_cases i
  · exact R.cherry_subset (pairEmbedding_mem _ _ 0)
  · exact R.cherry_subset (pairEmbedding_mem _ _ 1)
  · exact R.other_subset (pairEmbedding_mem _ _ 0)
  · exact R.other_subset (pairEmbedding_mem _ _ 1)

theorem BRole.embedding_mem_support {T : Finset α} (R : BRole T) (i : Fin 4) :
    R.embedding i ∈ T := by
  fin_cases i
  · exact R.cherry_subset (pairEmbedding_mem _ _ 0)
  · exact R.cherry_subset (pairEmbedding_mem _ _ 1)
  · exact R.tail_mem
  · exact R.selected_mem

#print axioms ACRole.embedding_first_range
#print axioms ACRole.embedding_last_range
#print axioms BRole.embedding_first_range
#print axioms BRole.embedding_two
#print axioms BRole.embedding_three
end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
