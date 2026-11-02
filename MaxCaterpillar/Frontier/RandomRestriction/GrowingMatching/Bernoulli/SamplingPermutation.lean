import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConfigurationsGeometry

/-! A literal label-to-position permutation for a selected set and actual tail
order. The selected order is the fixed faithful enumeration; no uniform full
permutation law is asserted for Bernoulli-selected sets. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
variable {n : ℕ}

noncomputable def labelsEquiv (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S))) :
    Fin (selectedCount S) ⊕ Fin (tailCount S) ≃ Fin n := by
  classical
  exact
    { toFun := fun x => match x with
        | Sum.inl i => keep S i
        | Sum.inr j => tail S (τ j)
      invFun := fun v => if h : v∈S then Sum.inl (keepIndex S v h)
        else Sum.inr (τ.symm (tailIndex S v h))
      left_inv := by
        intro x
        cases x with
        | inl i => simp only [dif_pos (keep_mem S i),keepIndex_keep]
        | inr j => simp only [dif_neg (tail_not_mem S (τ j)),tailIndex_tail,
            Equiv.symm_apply_apply]
      right_inv := by
        intro v
        by_cases h : v∈S
        · simp only [dif_pos h]
          exact keep_keepIndex S v h
        · simp only [dif_neg h,Equiv.apply_symm_apply]
          exact tail_tailIndex S v h }

/-- The only dimension cast: the proved actual complement/selected card identity. -/
def positionCast (S : Finset (Fin n)) : Fin (tailCount S+selectedCount S) ≃ Fin n :=
  finCongr (card_total S)

def positionEquiv (S : Finset (Fin n)) :
    Fin (selectedCount S) ⊕ Fin (tailCount S) ≃ Fin n :=
  (Configurations.fullPositionEquiv (selectedCount S) (tailCount S)).trans (positionCast S)

def selectedPosition (S : Finset (Fin n)) : Fin (selectedCount S) ↪ Fin n where
  toFun i := positionEquiv S (Sum.inl i)
  inj' := by intro i j h; exact Sum.inl.inj ((positionEquiv S).injective h)
def tailPosition (S : Finset (Fin n)) : Fin (tailCount S) ↪ Fin n where
  toFun j := positionEquiv S (Sum.inr j)
  inj' := by intro i j h; exact Sum.inr.inj ((positionEquiv S).injective h)

lemma selectedPosition_val (S : Finset (Fin n)) (i : Fin (selectedCount S)) :
    (selectedPosition S i).val=i.val := by
  change (finCongr (card_total S)
    (Configurations.fullPositionEquiv (selectedCount S) (tailCount S) (Sum.inl i))).val=i.val
  rw [finCongr_apply_coe,Configurations.fullPositionEquiv_selected]
  rfl
lemma tailPosition_val (S : Finset (Fin n)) (j : Fin (tailCount S)) :
    (tailPosition S j).val=j.val+selectedCount S := by
  change (finCongr (card_total S)
    (Configurations.fullPositionEquiv (selectedCount S) (tailCount S) (Sum.inr j))).val=j.val+selectedCount S
  rw [finCongr_apply_coe,Configurations.fullPositionEquiv_tail]
  rfl

noncomputable def fullPermutation (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S))) :
    Equiv.Perm (Fin n) := (labelsEquiv S τ).symm.trans (positionEquiv S)

lemma fullPermutation_selected (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (i : Fin (selectedCount S)) :
    (fullPermutation S τ).symm (selectedPosition S i)=keep S i := by
  change labelsEquiv S τ ((positionEquiv S).symm (positionEquiv S (Sum.inl i)))=keep S i
  rw [Equiv.symm_apply_apply]
  rfl
lemma fullPermutation_tail (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (j : Fin (tailCount S)) :
    (fullPermutation S τ).symm (tailPosition S j)=tail S (τ j) := by
  change labelsEquiv S τ ((positionEquiv S).symm (positionEquiv S (Sum.inr j)))=tail S (τ j)
  rw [Equiv.symm_apply_apply]
  rfl

lemma fullPermutation_apply_keep (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (i : Fin (selectedCount S)) : fullPermutation S τ (keep S i)=selectedPosition S i := by
  change positionEquiv S ((labelsEquiv S τ).symm (labelsEquiv S τ (Sum.inl i)))=selectedPosition S i
  rw [Equiv.symm_apply_apply]
  rfl
lemma fullPermutation_apply_tail (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (j : Fin (tailCount S)) : fullPermutation S τ (tail S (τ j))=tailPosition S j := by
  change positionEquiv S ((labelsEquiv S τ).symm (labelsEquiv S τ (Sum.inr j)))=tailPosition S j
  rw [Equiv.symm_apply_apply]
  rfl

/-- The literal prefix-selected labels are exactly the original finite set S. -/
lemma fullPermutation_selectedLabels (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S))) :
    GoodEvent.smallRankGaps (fullPermutation S τ) (selectedCount S)=S := by
  classical
  ext v
  rw [GoodEvent.mem_smallRankGaps]
  obtain ⟨x,rfl⟩ := (labelsEquiv S τ).surjective v
  cases x with
  | inl i =>
      change (fullPermutation S τ (keep S i)).val<selectedCount S ↔ keep S i∈S
      rw [fullPermutation_apply_keep,selectedPosition_val]
      exact iff_of_true i.isLt (keep_mem S i)
  | inr j =>
      change (fullPermutation S τ (tail S (τ j))).val<selectedCount S ↔ tail S (τ j)∈S
      rw [fullPermutation_apply_tail,tailPosition_val]
      exact iff_of_false (Nat.not_lt.mpr (Nat.le_add_left (selectedCount S) j.val))
        (tail_not_mem S (τ j))

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
