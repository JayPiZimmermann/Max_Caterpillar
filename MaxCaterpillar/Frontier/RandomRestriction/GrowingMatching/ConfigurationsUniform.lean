import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConfigurationsGeometry

/-! # Uniform actual permutation transport for an arbitrary selected block

This is an explicit finite product equivalence. In particular no conditional
law, local obstruction, or structural matching hypothesis enters the definitions. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
open BigOperators
variable {k m : ℕ}

/-- The genuine full-position permutation fixing all selected positions. -/
def tailLift (τ : TailPerm m) : FullPerm k m :=
  (fullPositionEquiv k m).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin k)) τ).trans (fullPositionEquiv k m))

@[simp] lemma tailLift_selected (τ : TailPerm m) (s : Fin k) :
    tailLift τ (selectedPosition k m s)=selectedPosition k m s := by
  change fullPositionEquiv k m ((Equiv.sumCongr (Equiv.refl (Fin k)) τ)
    ((fullPositionEquiv k m).symm (selectedPosition k m s)))=selectedPosition k m s
  rw [←fullPositionEquiv_selected,Equiv.symm_apply_apply]
  rfl

@[simp] lemma tailLift_tail (τ : TailPerm m) (j : Fin m) :
    tailLift τ (tailPosition k m j)=tailPosition k m (τ j) := by
  change fullPositionEquiv k m ((Equiv.sumCongr (Equiv.refl (Fin k)) τ)
    ((fullPositionEquiv k m).symm (tailPosition k m j)))=tailPosition k m (τ j)
  rw [←fullPositionEquiv_tail,Equiv.symm_apply_apply]
  exact fullPositionEquiv_tail k m (τ j)

lemma tailLift_symm_selected (τ : TailPerm m) (s : Fin k) :
    (tailLift τ).symm (selectedPosition k m s)=selectedPosition k m s := by
  apply (tailLift τ).injective
  rw [Equiv.apply_symm_apply,tailLift_selected]

lemma tailLift_symm_tail (τ : TailPerm m) (j : Fin m) :
    (tailLift τ.symm).symm (tailPosition k m j)=tailPosition k m (τ j) := by
  apply (tailLift τ.symm).injective
  rw [Equiv.apply_symm_apply,tailLift_tail,Equiv.symm_apply_apply]

lemma tailLift_selected_iff (τ : TailPerm m) (i : Fin (m+k)) :
    (tailLift τ i).val < k ↔ i.val < k := by
  rcases full_position_cases i with ⟨s,rfl⟩ | ⟨j,rfl⟩
  · rw [tailLift_selected]
  · rw [tailLift_tail]
    change (τ j).val+k<k ↔ j.val+k<k
    exact iff_of_false (not_lt_of_ge (Nat.le_add_left k (τ j).val))
      (not_lt_of_ge (Nat.le_add_left k j.val))

/-- Full permutation from original labels to their actual reordered positions. -/
def effectivePermutation (σ : FullPerm k m) (τ : TailPerm m) : FullPerm k m :=
  σ.trans (tailLift τ.symm)

/-- For every fixed tail permutation, effective full permutations are related
by an explicit bijection of the entire full-permutation space. -/
def effectiveFullEquiv (τ : TailPerm m) : FullPerm k m ≃ FullPerm k m where
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

lemma selectedLabels_effective (σ : FullPerm k m) (τ : TailPerm m) :
    selectedLabels (effectivePermutation σ τ)=selectedLabels σ := by
  ext v
  simp only [selectedLabels,GoodEvent.mem_smallRankGaps,effectivePermutation,
    Equiv.trans_apply,tailLift_selected_iff]

/-- Actual tail labels, after applying the independent tail permutation. -/
def actualTail (σ : FullPerm k m) (τ : TailPerm m) : Fin m ↪ Fin (m+k) where
  toFun j := baseTail σ (τ j)
  inj' := (baseTail σ).injective.comp τ.injective

lemma effectivePermutation_selected (σ : FullPerm k m) (τ : TailPerm m) (s : Fin k) :
    (effectivePermutation σ τ).symm (selectedPosition k m s)=σ.symm (selectedPosition k m s) := by
  change σ.symm ((tailLift τ.symm).symm (selectedPosition k m s))=_
  rw [tailLift_symm_selected]

lemma effectivePermutation_tail (σ : FullPerm k m) (τ : TailPerm m) (j : Fin m) :
    (effectivePermutation σ τ).symm (tailPosition k m j)=σ.symm (tailPosition k m (τ j)) := by
  change σ.symm ((tailLift τ.symm).symm (tailPosition k m j))=_
  rw [tailLift_symm_tail]

lemma baseTail_effective (σ : FullPerm k m) (τ : TailPerm m) :
    baseTail (effectivePermutation σ τ)=actualTail σ τ := by
  apply Function.Embedding.ext
  intro j
  exact effectivePermutation_tail σ τ j

/-- The literal two-permutation event coordinates of an actual configuration. -/
def effectiveConfiguration (ω : Configuration k m) : LiteralConfiguration k m :=
  (effectivePermutation ω.1 ω.2.1,ω.2.2)

/-- Reorder the finite product into a free tail permutation and the literal
full/rank coordinates. This is a bijection, not a distributional assumption. -/
def configurationEquiv (k m : ℕ) : Configuration k m ≃ TailPerm m × LiteralConfiguration k m where
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


/-- Literal pullback of any full/rank event to the actual three-permutation space. -/
noncomputable def pullbackEvent (B : Finset (LiteralConfiguration k m)) :
    Finset (Configuration k m) := by
  classical
  exact Finset.univ.filter (fun ω => effectiveConfiguration ω ∈ B)

@[simp] lemma mem_pullbackEvent (B : Finset (LiteralConfiguration k m)) (ω : Configuration k m) :
    ω ∈ pullbackEvent B ↔ effectiveConfiguration ω ∈ B := by
  classical
  simp only [pullbackEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- An explicit bijection of the actual event subtype with a free tail
permutation and the original literal event subtype. -/
noncomputable def pullbackEventEquiv (B : Finset (LiteralConfiguration k m)) :
    ↥(pullbackEvent B) ≃ TailPerm m × ↥B where
  toFun ω := (ω.val.2.1,⟨effectiveConfiguration ω.val,(mem_pullbackEvent B ω.val).mp ω.property⟩)
  invFun p := ⟨(configurationEquiv k m).symm (p.1,p.2.val),
    (mem_pullbackEvent B _).mpr (by
      have he := congrArg Prod.snd ((configurationEquiv k m).apply_symm_apply (p.1,p.2.val))
      change effectiveConfiguration ((configurationEquiv k m).symm (p.1,p.2.val))=p.2.val at he
      rw [he]
      exact p.2.property)⟩
  left_inv ω := by
    apply Subtype.ext
    exact (configurationEquiv k m).symm_apply_apply ω.val
  right_inv p := by
    have he := (configurationEquiv k m).apply_symm_apply (p.1,p.2.val)
    apply Prod.ext
    · change ((configurationEquiv k m) ((configurationEquiv k m).symm (p.1,p.2.val))).1=p.1
      exact congrArg Prod.fst he
    · apply Subtype.ext
      change ((configurationEquiv k m) ((configurationEquiv k m).symm (p.1,p.2.val))).2=p.2.val
      exact congrArg Prod.snd he

lemma pullbackEvent_card (B : Finset (LiteralConfiguration k m)) :
    (pullbackEvent B).card=Fintype.card (TailPerm m)*B.card := by
  calc
    _ = Fintype.card ↥(pullbackEvent B) := (Fintype.card_coe _).symm
    _ = Fintype.card (TailPerm m × ↥B) := Fintype.card_congr (pullbackEventEquiv B)
    _ = _ := by rw [Fintype.card_prod,Fintype.card_coe]

lemma card_configuration (k m : ℕ) :
    Fintype.card (Configuration k m)=
      Fintype.card (TailPerm m)*Fintype.card (LiteralConfiguration k m) := by
  calc
    _ = Fintype.card (TailPerm m × LiteralConfiguration k m) :=
      Fintype.card_congr (configurationEquiv k m)
    _ = _ := Fintype.card_prod _ _

/-- The literal event fraction is unchanged on the enlarged actual sample space. -/
lemma pullbackEvent_fraction (B : Finset (LiteralConfiguration k m)) :
    ((pullbackEvent B).card:ℝ)/(Fintype.card (Configuration k m):ℝ)=
      (B.card:ℝ)/(Fintype.card (LiteralConfiguration k m):ℝ) := by
  rw [pullbackEvent_card,card_configuration]
  simp only [Nat.cast_mul]
  apply mul_div_mul_left
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (TailPerm m) ≠ 0)

/-- The actual finite configuration fiber obtained by fixing σ and ρ. -/
abbrev FixedOuter (σ : FullPerm k m) (ρ : RankPerm m) :=
  {ω : Configuration k m // ω.1=σ ∧ ω.2.2=ρ}

def fixedOuterEquiv (σ : FullPerm k m) (ρ : RankPerm m) :
    TailPerm m ≃ FixedOuter σ ρ where
  toFun τ := ⟨(σ,(τ,ρ)),rfl,rfl⟩
  invFun ω := ω.val.2.1
  left_inv _ := rfl
  right_inv ω := by
    apply Subtype.ext
    exact Prod.ext ω.property.1.symm (Prod.ext rfl ω.property.2.symm)

lemma card_fixedOuter (σ : FullPerm k m) (ρ : RankPerm m) :
    Fintype.card (FixedOuter σ ρ)=Fintype.card (TailPerm m) :=
  Fintype.card_congr (fixedOuterEquiv σ ρ).symm

/-- Exact conditional finite averaging: σ and ρ are fixed parameters while τ
runs through every tail permutation once. This also holds for m=0. -/
lemma sum_fixedOuter (σ : FullPerm k m) (ρ : RankPerm m) (f : TailPerm m → ℝ) :
    (∑ ω : FixedOuter σ ρ,f ω.val.2.1)=∑ τ,f τ := by
  have h := Equiv.sum_comp (fixedOuterEquiv σ ρ) (fun ω : FixedOuter σ ρ => f ω.val.2.1)
  exact h.symm

lemma average_fixedOuter (σ : FullPerm k m) (ρ : RankPerm m) (f : TailPerm m → ℝ) :
    (∑ ω : FixedOuter σ ρ,f ω.val.2.1)/(Fintype.card (FixedOuter σ ρ):ℝ)=
      (∑ τ,f τ)/(Fintype.card (TailPerm m):ℝ) := by
  rw [sum_fixedOuter,card_fixedOuter]

/-- Exact product summation with the independent tail permutation innermost. -/
lemma sum_configuration_by_outer (f : Configuration k m → ℝ) :
    (∑ ω,f ω)=∑ σ : FullPerm k m,∑ ρ : RankPerm m,∑ τ : TailPerm m,f (σ,(τ,ρ)) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  exact Finset.sum_comm


end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
