import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Weights

/-! # Literal three-permutation configurations

A full permutation chooses the five selected labels. An independent tail
permutation reorders their complement, and a rank permutation chooses gaps.
The effective full permutation records that actual tail order without
changing any selected label. These definitions also apply at m=0. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Configurations
open GoodEvent GoodEventDominance

abbrev FullPerm (m : ℕ) := Equiv.Perm (Fin (m+5))
abbrev TailPerm (m : ℕ) := Equiv.Perm (Fin m)
abbrev RankPerm (m : ℕ) := Equiv.Perm (Fin m)
abbrev Configuration (m : ℕ) := FullPerm m × TailPerm m × RankPerm m
abbrev LiteralConfiguration (m : ℕ) := FullPerm m × RankPerm m

variable {m : ℕ}

/-- The genuine full-position permutation fixing all five selected positions. -/
def tailLift (τ : TailPerm m) : FullPerm m :=
  (fullPositionEquiv m).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 5)) τ).trans (fullPositionEquiv m))

@[simp] lemma tailLift_selected (τ : TailPerm m) (s : Fin 5) :
    tailLift τ (selectedPosition m s)=selectedPosition m s := by
  change fullPositionEquiv m ((Equiv.sumCongr (Equiv.refl (Fin 5)) τ)
    ((fullPositionEquiv m).symm (selectedPosition m s)))=selectedPosition m s
  rw [←fullPositionEquiv_selected,Equiv.symm_apply_apply]
  rfl

@[simp] lemma tailLift_tail (τ : TailPerm m) (j : Fin m) :
    tailLift τ (tailPosition m j)=tailPosition m (τ j) := by
  change fullPositionEquiv m ((Equiv.sumCongr (Equiv.refl (Fin 5)) τ)
    ((fullPositionEquiv m).symm (tailPosition m j)))=tailPosition m (τ j)
  rw [←fullPositionEquiv_tail,Equiv.symm_apply_apply]
  exact fullPositionEquiv_tail (τ j)

lemma tailLift_symm_selected (τ : TailPerm m) (s : Fin 5) :
    (tailLift τ).symm (selectedPosition m s)=selectedPosition m s := by
  apply (tailLift τ).injective
  rw [Equiv.apply_symm_apply,tailLift_selected]

lemma tailLift_symm_tail (τ : TailPerm m) (j : Fin m) :
    (tailLift τ.symm).symm (tailPosition m j)=tailPosition m (τ j) := by
  apply (tailLift τ.symm).injective
  rw [Equiv.apply_symm_apply,tailLift_tail,Equiv.symm_apply_apply]

lemma tailLift_selected_iff (τ : TailPerm m) (i : Fin (m+5)) :
    (tailLift τ i).val < 5 ↔ i.val < 5 := by
  rcases full_position_cases i with ⟨s,rfl⟩ | ⟨j,rfl⟩
  · rw [tailLift_selected]
  · rw [tailLift_tail]
    change (τ j).val+5<5 ↔ j.val+5<5
    exact iff_of_false (not_lt_of_ge (Nat.le_add_left 5 (τ j).val))
      (not_lt_of_ge (Nat.le_add_left 5 j.val))

/-- Full permutation from original labels to their actual reordered positions. -/
def effectivePermutation (σ : FullPerm m) (τ : TailPerm m) : FullPerm m :=
  σ.trans (tailLift τ.symm)

/-- For every fixed tail permutation, effective full permutations are related
by an explicit bijection of the entire full-permutation space. -/
def effectiveFullEquiv (τ : TailPerm m) : FullPerm m ≃ FullPerm m where
  toFun σ := effectivePermutation σ τ
  invFun σ := σ.trans (tailLift τ.symm).symm
  left_inv σ := by
    apply Equiv.ext
    intro v
    change (tailLift τ.symm).symm (tailLift τ.symm (σ v))=σ v
    exact Equiv.symm_apply_apply _ _
  right_inv σ := by
    apply Equiv.ext
    intro v
    change tailLift τ.symm ((tailLift τ.symm).symm (σ v))=σ v
    exact Equiv.apply_symm_apply _ _

noncomputable def selectedSet (σ : FullPerm m) : Finset (Fin (m+5)) :=
  Finset.univ.filter (fun v => (σ v).val<5)

lemma selectedSet_effective (σ : FullPerm m) (τ : TailPerm m) :
    selectedSet (effectivePermutation σ τ)=selectedSet σ := by
  ext v
  simp only [selectedSet,Finset.mem_filter,Finset.mem_univ,true_and,
    effectivePermutation,Equiv.trans_apply,tailLift_selected_iff]

/-- Base complement enumeration in the full permutation. -/
def baseTail (σ : FullPerm m) : Fin m ↪ Fin (m+5) where
  toFun j := σ.symm (tailPosition m j)
  inj' := σ.symm.injective.comp (tailPosition m).injective

/-- Actual tail labels, after applying the independent tail permutation. -/
def actualTail (σ : FullPerm m) (τ : TailPerm m) : Fin m ↪ Fin (m+5) where
  toFun j := baseTail σ (τ j)
  inj' := (baseTail σ).injective.comp τ.injective

lemma effectivePermutation_selected (σ : FullPerm m) (τ : TailPerm m) (s : Fin 5) :
    (effectivePermutation σ τ).symm (selectedPosition m s)=σ.symm (selectedPosition m s) := by
  change σ.symm ((tailLift τ.symm).symm (selectedPosition m s))=_
  rw [tailLift_symm_selected]

lemma effectivePermutation_tail (σ : FullPerm m) (τ : TailPerm m) (j : Fin m) :
    (effectivePermutation σ τ).symm (tailPosition m j)=σ.symm (tailPosition m (τ j)) := by
  change σ.symm ((tailLift τ.symm).symm (tailPosition m j))=_
  rw [tailLift_symm_tail]

lemma baseTail_effective (σ : FullPerm m) (τ : TailPerm m) :
    baseTail (effectivePermutation σ τ)=actualTail σ τ := by
  apply Function.Embedding.ext
  intro j
  exact effectivePermutation_tail σ τ j

/-- The literal two-permutation event coordinates of an actual configuration. -/
def effectiveConfiguration (ω : Configuration m) : LiteralConfiguration m :=
  (effectivePermutation ω.1 ω.2.1,ω.2.2)

/-- Reorder the finite product into a free tail permutation and the literal
full/rank coordinates. This is a bijection, not a distributional assumption. -/
def configurationEquiv (m : ℕ) : Configuration m ≃ TailPerm m × LiteralConfiguration m where
  toFun ω := (ω.2.1,effectiveConfiguration ω)
  invFun p := ((effectiveFullEquiv p.1).symm p.2.1,(p.1,p.2.2))
  left_inv ω := by
    rcases ω with ⟨σ,τ,ρ⟩
    change ((effectiveFullEquiv τ).symm ((effectiveFullEquiv τ) σ),(τ,ρ))=(σ,(τ,ρ))
    rw [Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨τ,σ,ρ⟩
    change (τ,((effectiveFullEquiv τ) ((effectiveFullEquiv τ).symm σ),ρ))=(τ,(σ,ρ))
    rw [Equiv.apply_symm_apply]

end MaxCaterpillar.Frontier.RandomRestriction.Configurations
