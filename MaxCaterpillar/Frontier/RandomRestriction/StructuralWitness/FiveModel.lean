import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Reindex
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.LocalizedModel

/-! The actual dominant-gap local model, identified bijectively with five
selected inputs. Original first and outer indices and coefficients remain. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
open BigOperators DominantGap Cartesian
variable {N h₁ h₂ : ℕ}

noncomputable def fiveEquiv (S : Finset (Fin N)) (hS : S.card=5) : Fin 5 ≃ Fin S.card :=
  Fin.castIso hS.symm

noncomputable def fiveEmbedding (S : Finset (Fin N)) (hS : S.card=5) : Fin 5 ↪ Fin N :=
  (fiveEquiv S hS).toEmbedding.trans (NormalizedNetwork.selectedEmbedding S)

lemma fiveEmbedding_image (S : Finset (Fin N)) (hS : S.card=5) :
    Finset.univ.image (fiveEmbedding S hS)=S := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
    rw [← NormalizedNetwork.selectedEmbedding_image S]
    exact Finset.mem_image.mpr ⟨fiveEquiv S hS i,Finset.mem_univ _,hi⟩
  · intro hv
    rw [← NormalizedNetwork.selectedEmbedding_image S] at hv
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨(fiveEquiv S hS).symm i,Finset.mem_univ _,?_⟩
    change NormalizedNetwork.selectedEmbedding S
      (fiveEquiv S hS ((fiveEquiv S hS).symm i))=v
    rw [Equiv.apply_symm_apply]
    exact hi

noncomputable def fiveModel (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (hS : S.card=5) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ) :
    NormalizedNetwork 5 h₁ h₂ :=
  reindexInputs (localizedModel net S p T) (fiveEquiv S hS)

lemma fiveModel_A (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (hS : S.card=5) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (j : Fin h₁) :
    (fiveModel net S hS p T).A j=
      if NormalizedNetwork.rowSupport (net.A j)⊆S
      then NormalizedNetwork.restrict (fiveEmbedding S hS) (net.A j) else 0 := by
  classical
  funext i
  change (localizedModel net S p T).A j (fiveEquiv S hS i)=_
  rw [localizedModel_A net S p T h j]
  by_cases hj : NormalizedNetwork.rowSupport (net.A j)⊆S
  · rw [if_pos hj,if_pos hj]
    rfl
  · rw [if_neg hj,if_neg hj]
    rfl

lemma fiveModel_A_mask (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (hS : S.card=5) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (j : Fin h₁) :
    (fiveModel net S hS p T).A j=
      if NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image (fiveEmbedding S hS)
      then NormalizedNetwork.restrict (fiveEmbedding S hS) (net.A j) else 0 := by
  rw [fiveEmbedding_image]
  exact fiveModel_A net S hS p T h j

lemma fiveModel_computes_max [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hnet : ∀ x,net.eval x=Maximum N x) (S : Finset (Fin N)) (hS : S.card=5)
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    ∀ x,(fiveModel net S hS p T).eval x=Maximum 5 x := by
  have hpos : 0<S.card := by rw [hS]; decide
  letI : NeZero S.card := ⟨Nat.ne_of_gt hpos⟩
  exact reindexInputs_computes_max _ _
    (localizedModel_computes_max net hnet S (Finset.card_pos.mp hpos) p T h)

lemma fiveModel_translation_normalized [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (hnet : ∀ x,net.eval x=Maximum N x)
    (S : Finset (Fin N)) (hS : S.card=5)
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    (fiveModel net S hS p T).TranslationNormalized := by
  have hpos : 0<S.card := by rw [hS]; decide
  exact reindexInputs_translation_normalized _ _
    (localizedModel_translation_normalized net hn hnet S (Finset.card_pos.mp hpos) p T h)

lemma fiveModel_support_le_two (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (hS : S.card=5) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T)
    (hno : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆S) :
    ∀ j,(NormalizedNetwork.rowSupport ((fiveModel net S hS p T).A j)).card≤2 := by
  classical
  intro j
  rw [fiveModel_A net S hS p T h j]
  by_cases hj : NormalizedNetwork.rowSupport (net.A j)⊆S
  · rw [if_pos hj,NormalizedNetwork.card_rowSupport_restrict]
    · have hn : ¬3≤(NormalizedNetwork.rowSupport (net.A j)).card := fun hn => hno j hn hj
      exact Nat.le_of_lt_succ (lt_of_not_ge hn)
    · rw [fiveEmbedding_image]
      exact hj
  · rw [if_neg hj,NormalizedNetwork.rowSupport_zero,Finset.card_empty]
    exact Nat.zero_le _

/-- A dead original outer slot has literally zero local W,U,d, rather than
being deleted or replaced by an existentially chosen neuron. -/
lemma fiveModel_dead (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (hS : S.card=5) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (k : Fin h₂) (hk : net.inner k (setGapPoint S p T)≠0) :
    (∀ j,(fiveModel net S hS p T).W k j=0) ∧
      (fiveModel net S hS p T).U k=0 ∧ (fiveModel net S hS p T).d k=0 := by
  classical
  constructor
  · intro j
    change (if net.inner k (setGapPoint S p T)=0 then _ else 0)=0
    exact if_neg hk
  · constructor
    · funext i
      change (if net.inner k (setGapPoint S p T)=0 then
        (net.localFirst (setGapPoint S p T) (NormalizedNetwork.selectedEmbedding S)).U k
        else (0 : Point S.card)) (fiveEquiv S hS i)=0
      rw [if_neg hk]
      rfl
    · change (if net.inner k (setGapPoint S p T)=0 then _ else 0)=0
      exact if_neg hk

lemma fiveModel_W_retained (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (hS : S.card=5) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (k : Fin h₂)
    (hk : net.inner k (setGapPoint S p T)=0) (j : Fin h₁)
    (hj : NormalizedNetwork.rowSupport (net.A j)⊆S) :
    (fiveModel net S hS p T).W k j=net.W k j := by
  classical
  change (if net.inner k (setGapPoint S p T)=0 then
    (if lin (net.A j) (setGapPoint S p T)=0 then net.W k j else 0) else 0)=_
  rw [if_pos hk,if_pos ((h.first_zero_iff_support j).mpr hj)]

#print axioms fiveModel_computes_max
#print axioms fiveModel_translation_normalized
#print axioms fiveModel_support_le_two
#print axioms fiveModel_dead
end MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
