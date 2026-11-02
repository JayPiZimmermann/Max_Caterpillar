import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.SetRealization
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Localization

/-! # Faithful actual localization at the common dominant-gap point

The model below is literally the original indexed network localized at
`setGapPoint S p T` along the canonical selected-coordinate embedding. All
masks and skip coefficients are derived from the proved generic-point data.
No replacement network, assumed mask, or assumed nonlinear survival law is
introduced. Every original first and second neuron index is retained.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

variable {N m h₁ h₂ : ℕ}

noncomputable def restrictSelected (S : Finset (Fin N)) (a : Point N) : Point S.card :=
  NormalizedNetwork.restrict (NormalizedNetwork.selectedEmbedding S) a

/-- The actual local model, not an existentially chosen normalized replacement. -/
noncomputable def localizedModel (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ) :
    NormalizedNetwork S.card h₁ h₂ :=
  net.localize (setGapPoint S p T) (NormalizedNetwork.selectedEmbedding S)

/-- The local first pass's linear skip is the exact restricted actual effective
row, including every original linear skip and active first-neuron contribution. -/
theorem localFirst_U_eq_restrict_actualEffectiveRow (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (k : Fin h₂) :
    (net.localFirst q e).U k=NormalizedNetwork.restrict e (actualEffectiveRow net k q) := by
  classical
  change NormalizedNetwork.restrict e (net.U k)+net.firstLinear q e (net.W k)=_
  funext i
  simp only [NormalizedNetwork.restrict,NormalizedNetwork.firstLinear,
    actualEffectiveRow,effectiveRow,Pi.add_apply,Finset.sum_apply]
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : 0<lin (net.A j) q
  · have hb : activePattern net q j=true := (activePattern_eq_true net q j).mpr hp
    simp only [if_pos hp,if_pos hb,Pi.smul_apply,smul_eq_mul,NormalizedNetwork.restrict]
    rfl
  · have hb : activePattern net q j≠true := fun h => hp ((activePattern_eq_true net q j).mp h)
    simp only [if_neg hp,if_neg hb,Pi.zero_apply]

/-- Exact first-row survival mask in the original first-neuron index type. -/
theorem localizedModel_A (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (j : Fin h₁) :
    (localizedModel net S p T).A j=
      if NormalizedNetwork.rowSupport (net.A j)⊆S then restrictSelected S (net.A j) else 0 := by
  classical
  rw [localizedModel,NormalizedNetwork.localize_first_row]
  by_cases hj : NormalizedNetwork.rowSupport (net.A j)⊆S
  · rw [if_pos ((h.first_zero_iff_support j).mpr hj),if_pos hj]
    rfl
  · rw [if_neg (fun hz => hj ((h.first_zero_iff_support j).mp hz)),if_neg hj]

/-- Exact first-to-second coefficients: both actual rows must survive. -/
theorem localizedModel_W (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (k : Fin h₂) (j : Fin h₁) :
    (localizedModel net S p T).W k j=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S ∧
        NormalizedNetwork.rowSupport (net.A j)⊆S then net.W k j else 0 := by
  classical
  change (if net.inner k (setGapPoint S p T)=0 then
    (if lin (net.A j) (setGapPoint S p T)=0 then net.W k j else 0) else 0)=_
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
  · have hk0 := (h.second_zero_iff_support k).mpr hk
    by_cases hj : NormalizedNetwork.rowSupport (net.A j)⊆S
    · have hj0 := (h.first_zero_iff_support j).mpr hj
      simp [hk0,hj0,hk,hj]
    · have hj0 : lin (net.A j) (setGapPoint S p T)≠0 :=
        fun hz => hj ((h.first_zero_iff_support j).mp hz)
      simp [hk0,hj0,hk,hj]
  · have hk0 : net.inner k (setGapPoint S p T)≠0 :=
      fun hz => hk ((h.second_zero_iff_support k).mp hz)
    simp [hk0,hk]

/-- Exact surviving linear skips are actual restricted effective rows. -/
theorem localizedModel_U (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (k : Fin h₂) :
    (localizedModel net S p T).U k=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
        then restrictSelected S (actualEffectiveRow net k (setGapPoint S p T)) else 0 := by
  classical
  change (if net.inner k (setGapPoint S p T)=0 then
    (net.localFirst (setGapPoint S p T) (NormalizedNetwork.selectedEmbedding S)).U k else 0)=_
  rw [localFirst_U_eq_restrict_actualEffectiveRow]
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
  · rw [if_pos ((h.second_zero_iff_support k).mpr hk),if_pos hk]
    rfl
  · rw [if_neg (fun hz => hk ((h.second_zero_iff_support k).mp hz)),if_neg hk]

/-- Original second output coefficients are either retained unchanged or masked. -/
theorem localizedModel_d (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (k : Fin h₂) :
    (localizedModel net S p T).d k=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
        then net.d k else 0 := by
  classical
  change (if net.inner k (setGapPoint S p T)=0 then net.d k else 0)=_
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
  · rw [if_pos ((h.second_zero_iff_support k).mpr hk),if_pos hk]
  · rw [if_neg (fun hz => hk ((h.second_zero_iff_support k).mp hz)),if_neg hk]

theorem localizedModel_W_of_surviving (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (k : Fin h₂)
    (hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S)
    (j : Fin h₁) :
    (localizedModel net S p T).W k j=
      if NormalizedNetwork.rowSupport (net.A j)⊆S then net.W k j else 0 := by
  classical
  rw [localizedModel_W net S p T h k j]
  simp only [hk,true_and]

theorem localizedModel_W_of_surviving_retained (net : NormalizedNetwork N h₁ h₂)
    (S : Finset (Fin N)) (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (k : Fin h₂)
    (hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S)
    (j : Fin h₁) (hj : NormalizedNetwork.rowSupport (net.A j)⊆S) :
    (localizedModel net S p T).W k j=net.W k j := by
  rw [localizedModel_W_of_surviving net S p T h k hk j,if_pos hj]

/-- Localization cannot create a new feeding first-neuron index. -/
theorem localizedModel_feeding_original (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (j : Fin h₁) (hj : (localizedModel net S p T).Feeding j) : net.Feeding j :=
  net.localize_feeding_original (setGapPoint S p T) (NormalizedNetwork.selectedEmbedding S) j hj

/-- First-row coordinate sums are preserved exactly on the retained support. -/
theorem localizedModel_first_zero_sum (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    ∀ j,∑ i,(localizedModel net S p T).A j i=0 := by
  apply net.localize_first_zero_sum hn.1 (NormalizedNetwork.selectedEmbedding S) (setGapPoint S p T)
  intro j
  simpa only [NormalizedNetwork.selectedEmbedding_image] using h.first_zero_iff_support j

/-- Surviving actual effective rows also retain their full zero coordinate sum. -/
theorem localizedModel_U_zero_sum (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    ∀ k,∑ i,(localizedModel net S p T).U k i=0 := by
  classical
  intro k
  rw [localizedModel_U net S p T h k]
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
  · rw [if_pos hk]
    change (∑ i,NormalizedNetwork.restrict (NormalizedNetwork.selectedEmbedding S)
      (actualEffectiveRow net k (setGapPoint S p T)) i)=0
    rw [NormalizedNetwork.sum_restrict_of_subset _ _ (by
      simpa only [NormalizedNetwork.selectedEmbedding_image] using hk)]
    exact effectiveRow_zero_sum net hn (activePattern net (setGapPoint S p T)) k
  · rw [if_neg hk]
    simp

/-- A zero-sum second-skip array makes outer normalization literally the identity. -/
theorem normalizeOuter_eq_self_of_zero_sum_U (model : NormalizedNetwork m h₁ h₂)
    (hU : ∀ k,∑ i,model.U k i=0) : NormalizedNetwork.normalizeOuter model=model := by
  cases model with
  | mk A U W L B d =>
    change (∀ k,∑ i,U k i=0) at hU
    simp [NormalizedNetwork.normalizeOuter,NormalizedNetwork.freezeOuter,hU]

theorem localizedModel_normalizeOuter_eq_self (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    NormalizedNetwork.normalizeOuter (localizedModel net S p T)=localizedModel net S p T :=
  normalizeOuter_eq_self_of_zero_sum_U _ (localizedModel_U_zero_sum net hn S p T h)

/-- The actual constructed gap point yields the full all-input selected MAX. -/
theorem localizedModel_computes_max [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hnet : ∀ x,net.eval x=Maximum N x) (S : Finset (Fin N)) (hS : S.Nonempty)
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    letI : NeZero S.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hS)⟩
    ∀ x,(localizedModel net S p T).eval x=Maximum S.card x := by
  letI : NeZero S.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hS)⟩
  apply net.localize_computes_max_of_tied hnet (NormalizedNetwork.selectedEmbedding S) (setGapPoint S p T)
  · intro a
    apply h.selected_zero
    change (S.equivFin.symm a).val∈S
    exact (S.equivFin.symm a).property
  · intro i hi
    apply h.outside_negative i
    simpa only [NormalizedNetwork.selectedEmbedding_image] using hi

/-- The faithful local model itself is translation normalized; no further
normalization can alter its masks or original coefficients. -/
theorem localizedModel_translation_normalized [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (hnet : ∀ x,net.eval x=Maximum N x)
    (S : Finset (Fin N)) (hS : S.Nonempty)
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) : (localizedModel net S p T).TranslationNormalized := by
  letI : NeZero S.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hS)⟩
  have hnorm := NormalizedNetwork.normalizeOuter_translation_normalized (localizedModel net S p T)
    (localizedModel_first_zero_sum net hn S p T h) (localizedModel_computes_max net hnet S hS p T h)
  rw [localizedModel_normalizeOuter_eq_self net hn S p T h] at hnorm
  exact hnorm

/-- The support budget charges only unchanged original large-support rows
whose entire original support lies in the selected coordinate set. -/
theorem localizedModel_support_cost_le (net : NormalizedNetwork N h₁ h₂) (S : Finset (Fin N))
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) (cost : ℕ→ℕ) :
    (∑ j,if 3≤(NormalizedNetwork.rowSupport ((localizedModel net S p T).A j)).card
      then cost (NormalizedNetwork.rowSupport ((localizedModel net S p T).A j)).card else 0)≤
    ∑ j,if 3≤(NormalizedNetwork.rowSupport (net.A j)).card ∧ NormalizedNetwork.rowSupport (net.A j)⊆S
      then cost (NormalizedNetwork.rowSupport (net.A j)).card else 0 := by
  classical
  have hb := NormalizedNetwork.indexed_support_cost_le_of_masked_restriction
    (NormalizedNetwork.selectedEmbedding S) net.A (localizedModel net S p T).A
    (fun j => NormalizedNetwork.rowSupport (net.A j)⊆S) cost
    (by intro j hj; simpa only [NormalizedNetwork.selectedEmbedding_image] using hj)
    (localizedModel_A net S p T h)
  simpa only [NormalizedNetwork.selectedEmbedding_image] using hb

/-- Complete faithful specification of this actual indexed localization. -/
theorem localizedModel_spec [NeZero N] (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) (S : Finset (Fin N)) (hS : S.Nonempty)
    (p : RawConfig ((Finset.univ : Finset (Fin N)) \ S).card) (T : ℝ)
    (h : GenericSetNetworkPoint net S p T) :
    letI : NeZero S.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hS)⟩
    (∀ x,(localizedModel net S p T).eval x=Maximum S.card x) ∧
    (localizedModel net S p T).TranslationNormalized ∧
    (∀ j,(localizedModel net S p T).A j=
      if NormalizedNetwork.rowSupport (net.A j)⊆S then restrictSelected S (net.A j) else 0) ∧
    (∀ k j,(localizedModel net S p T).W k j=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S ∧
        NormalizedNetwork.rowSupport (net.A j)⊆S then net.W k j else 0) ∧
    (∀ k,(localizedModel net S p T).U k=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S
        then restrictSelected S (actualEffectiveRow net k (setGapPoint S p T)) else 0) ∧
    (∀ k,(localizedModel net S p T).d k=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (setGapPoint S p T))⊆S then net.d k else 0) ∧
    (∀ j,(localizedModel net S p T).Feeding j→net.Feeding j) ∧
    (∀ cost : ℕ→ℕ,
      (∑ j,if 3≤(NormalizedNetwork.rowSupport ((localizedModel net S p T).A j)).card
        then cost (NormalizedNetwork.rowSupport ((localizedModel net S p T).A j)).card else 0)≤
      ∑ j,if 3≤(NormalizedNetwork.rowSupport (net.A j)).card ∧ NormalizedNetwork.rowSupport (net.A j)⊆S
        then cost (NormalizedNetwork.rowSupport (net.A j)).card else 0) := by
  letI : NeZero S.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hS)⟩
  exact ⟨localizedModel_computes_max net hnet S hS p T h,
    localizedModel_translation_normalized net hn hnet S hS p T h,
    localizedModel_A net S p T h,localizedModel_W net S p T h,
    localizedModel_U net S p T h,localizedModel_d net S p T h,
    localizedModel_feeding_original net S p T,localizedModel_support_cost_le net S p T h⟩
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
