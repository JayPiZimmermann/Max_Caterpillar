import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.LocalizedModel

/-! # Faithful localization for arbitrary complementary keep and tail embeddings

The localized network is the literal original network at the actual embedded
random gap point. Neither the kept coordinates nor the tail are reindexed to
a canonical finset representation. Original first and second indices stay fixed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian
variable {N r m h₁ h₂ : ℕ}

/-- The selected output coordinates and the actual tail embedding are independent
inputs. Complementarity is proved separately rather than built into this model. -/
noncomputable def embeddedLocalizedModel (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ) :
    NormalizedNetwork r h₁ h₂ := net.localize (actualGapPoint e p T) f

/-- Pure coordinate equivalence for any two complementary embeddings. -/
theorem restrict_complementary_tail_zero_iff_support (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (a : Point N) :
    NormalizedNetwork.restrict e a=0 ↔ NormalizedNetwork.rowSupport a⊆Finset.univ.image f := by
  classical
  constructor
  · intro hz i hi
    by_contra hnot
    have hitail : i∈Finset.univ.image e := by
      rw [hcomp]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnot⟩
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hitail
    have hval := congrFun hz j
    change a (e j)=0 at hval
    rw [hj] at hval
    exact (NormalizedNetwork.mem_rowSupport a i).mp hi hval
  · intro hs
    funext j
    change a (e j)=0
    by_contra hn
    have hkeep := hs ((NormalizedNetwork.mem_rowSupport a (e j)).mpr hn)
    have htail : e j∈Finset.univ.image e := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    rw [hcomp] at htail
    exact (Finset.mem_sdiff.mp htail).2 hkeep

theorem embedded_selected_zero (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) : ∀ a,actualGapPoint e p T (f a)=0 := by
  classical
  intro a
  apply h.tied_block
  intro htail
  rw [hcomp] at htail
  exact (Finset.mem_sdiff.mp htail).2 (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)

theorem embedded_outside_negative (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) :
    ∀ i,i∉Finset.univ.image f→actualGapPoint e p T i<0 := by
  classical
  intro i hi
  have htail : i∈Finset.univ.image e := by
    rw [hcomp]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp htail
  have hn := h.negative_tail a
  rwa [ha] at hn

theorem embedded_first_zero_iff_support (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (j : Fin h₁) :
    lin (net.A j) (actualGapPoint e p T)=0 ↔ NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f :=
  (h.first_zero_iff j).trans (restrict_complementary_tail_zero_iff_support f e hcomp (net.A j))

theorem embedded_second_zero_iff_support (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (k : Fin h₂) :
    net.inner k (actualGapPoint e p T)=0 ↔
      NormalizedNetwork.rowSupport (actualEffectiveRow net k (actualGapPoint e p T))⊆Finset.univ.image f :=
  (h.second_zero_iff k).trans (restrict_complementary_tail_zero_iff_support f e hcomp _)

section ArbitraryPoint
variable (net : NormalizedNetwork N h₁ h₂) (f : Fin r ↪ Fin N) (q : Point N)

/-- Generic exact first mask for any point whose support criterion is proved. -/
theorem localize_A_of_support_criterion
    (hA : ∀ j,lin (net.A j) q=0 ↔ NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f)
    (j : Fin h₁) :
    (net.localize q f).A j=if NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f
      then NormalizedNetwork.restrict f (net.A j) else 0 := by
  classical
  rw [NormalizedNetwork.localize_first_row]
  by_cases hj : NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f
  · rw [if_pos ((hA j).mpr hj),if_pos hj]
  · rw [if_neg (fun hz => hj ((hA j).mp hz)),if_neg hj]

/-- Generic exact nonlinear weight mask, with both original supports checked. -/
theorem localize_W_of_support_criteria
    (hA : ∀ j,lin (net.A j) q=0 ↔ NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f)
    (hV : ∀ k,net.inner k q=0 ↔ NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f)
    (k : Fin h₂) (j : Fin h₁) :
    (net.localize q f).W k j=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f ∧
        NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f then net.W k j else 0 := by
  classical
  change (if net.inner k q=0 then (if lin (net.A j) q=0 then net.W k j else 0) else 0)=_
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f
  · have hk0 := (hV k).mpr hk
    by_cases hj : NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f
    · have hj0 := (hA j).mpr hj
      simp [hk0,hj0,hk,hj]
    · have hj0 : lin (net.A j) q≠0 := fun hz => hj ((hA j).mp hz)
      simp [hk0,hj0,hk,hj]
  · have hk0 : net.inner k q≠0 := fun hz => hk ((hV k).mp hz)
    simp [hk0,hk]

/-- The retained actual skip is the restricted actual effective row. -/
theorem localize_U_of_support_criterion
    (hV : ∀ k,net.inner k q=0 ↔ NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f)
    (k : Fin h₂) :
    (net.localize q f).U k=if NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f
      then NormalizedNetwork.restrict f (actualEffectiveRow net k q) else 0 := by
  classical
  change (if net.inner k q=0 then (net.localFirst q f).U k else 0)=_
  rw [localFirst_U_eq_restrict_actualEffectiveRow]
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f
  · rw [if_pos ((hV k).mpr hk),if_pos hk]
  · rw [if_neg (fun hz => hk ((hV k).mp hz)),if_neg hk]

theorem localize_d_of_support_criterion
    (hV : ∀ k,net.inner k q=0 ↔ NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f)
    (k : Fin h₂) :
    (net.localize q f).d k=if NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f
      then net.d k else 0 := by
  classical
  change (if net.inner k q=0 then net.d k else 0)=_
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f
  · rw [if_pos ((hV k).mpr hk),if_pos hk]
  · rw [if_neg (fun hz => hk ((hV k).mp hz)),if_neg hk]

theorem localize_U_zero_sum_of_support_criterion (hn : net.TranslationNormalized)
    (hV : ∀ k,net.inner k q=0 ↔ NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f) :
    ∀ k,∑ i,(net.localize q f).U k i=0 := by
  classical
  intro k
  rw [localize_U_of_support_criterion net f q hV k]
  by_cases hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f
  · rw [if_pos hk,NormalizedNetwork.sum_restrict_of_subset f _ hk]
    exact effectiveRow_zero_sum net hn (activePattern net q) k
  · rw [if_neg hk]
    simp

/-- General proof core: faithful actual localization is normalized whenever
its first and effective-second support criteria and tied coordinates are proved. -/
theorem localize_translation_normalized_of_support_criteria [NeZero N] [NeZero r]
    (hn : net.TranslationNormalized) (hnet : ∀ x,net.eval x=Maximum N x)
    (hA : ∀ j,lin (net.A j) q=0 ↔ NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f)
    (hV : ∀ k,net.inner k q=0 ↔ NormalizedNetwork.rowSupport (actualEffectiveRow net k q)⊆Finset.univ.image f)
    (hq : ∀ a,q (f a)=0) (hneg : ∀ i,i∉Finset.univ.image f→q i<0) :
    (net.localize q f).TranslationNormalized := by
  have hmax := net.localize_computes_max_of_tied hnet f q hq hneg
  have hfirst := net.localize_first_zero_sum hn.1 f q hA
  have hU := localize_U_zero_sum_of_support_criterion net f q hn hV
  have hself := normalizeOuter_eq_self_of_zero_sum_U (net.localize q f) hU
  have hnorm := NormalizedNetwork.normalizeOuter_translation_normalized (net.localize q f) hfirst hmax
  rw [hself] at hnorm
  exact hnorm
end ArbitraryPoint

theorem embeddedLocalizedModel_A (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (j : Fin h₁) :
    (embeddedLocalizedModel net f e p T).A j=
      if NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f
        then NormalizedNetwork.restrict f (net.A j) else 0 :=
  localize_A_of_support_criterion net f _ (embedded_first_zero_iff_support net f e p T hcomp h) j

theorem embeddedLocalizedModel_W (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (k : Fin h₂) (j : Fin h₁) :
    (embeddedLocalizedModel net f e p T).W k j=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (actualGapPoint e p T))⊆Finset.univ.image f ∧
        NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f then net.W k j else 0 :=
  localize_W_of_support_criteria net f _ (embedded_first_zero_iff_support net f e p T hcomp h)
    (embedded_second_zero_iff_support net f e p T hcomp h) k j

theorem embeddedLocalizedModel_U (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (k : Fin h₂) :
    (embeddedLocalizedModel net f e p T).U k=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (actualGapPoint e p T))⊆Finset.univ.image f
        then NormalizedNetwork.restrict f (actualEffectiveRow net k (actualGapPoint e p T)) else 0 :=
  localize_U_of_support_criterion net f _ (embedded_second_zero_iff_support net f e p T hcomp h) k

theorem embeddedLocalizedModel_d (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (k : Fin h₂) :
    (embeddedLocalizedModel net f e p T).d k=
      if NormalizedNetwork.rowSupport (actualEffectiveRow net k (actualGapPoint e p T))⊆Finset.univ.image f
        then net.d k else 0 :=
  localize_d_of_support_criterion net f _ (embedded_second_zero_iff_support net f e p T hcomp h) k

theorem embeddedLocalizedModel_W_of_surviving (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (k : Fin h₂)
    (hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (actualGapPoint e p T))⊆Finset.univ.image f)
    (j : Fin h₁) :
    (embeddedLocalizedModel net f e p T).W k j=
      if NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f then net.W k j else 0 := by
  classical
  rw [embeddedLocalizedModel_W net f e p T hcomp h k j]
  simp only [hk,true_and]

theorem embeddedLocalizedModel_W_of_surviving_retained (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (k : Fin h₂)
    (hk : NormalizedNetwork.rowSupport (actualEffectiveRow net k (actualGapPoint e p T))⊆Finset.univ.image f)
    (j : Fin h₁) (hj : NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f) :
    (embeddedLocalizedModel net f e p T).W k j=net.W k j := by
  rw [embeddedLocalizedModel_W_of_surviving net f e p T hcomp h k hk j,if_pos hj]

theorem embeddedLocalizedModel_U_zero_sum (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) : ∀ k,∑ i,(embeddedLocalizedModel net f e p T).U k i=0 :=
  localize_U_zero_sum_of_support_criterion net f _ hn (embedded_second_zero_iff_support net f e p T hcomp h)

theorem embeddedLocalizedModel_normalizeOuter_eq_self (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) :
    NormalizedNetwork.normalizeOuter (embeddedLocalizedModel net f e p T)=embeddedLocalizedModel net f e p T :=
  normalizeOuter_eq_self_of_zero_sum_U _ (embeddedLocalizedModel_U_zero_sum net hn f e p T hcomp h)

theorem embeddedLocalizedModel_computes_max [NeZero N] [NeZero r]
    (net : NormalizedNetwork N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) :
    ∀ x,(embeddedLocalizedModel net f e p T).eval x=Maximum r x :=
  net.localize_computes_max_of_tied hnet f _ (embedded_selected_zero net f e p T hcomp h)
    (embedded_outside_negative net f e p T hcomp h)

theorem embeddedLocalizedModel_translation_normalized [NeZero N] [NeZero r]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) :
    (embeddedLocalizedModel net f e p T).TranslationNormalized :=
  localize_translation_normalized_of_support_criteria net f _ hn hnet
    (embedded_first_zero_iff_support net f e p T hcomp h)
    (embedded_second_zero_iff_support net f e p T hcomp h)
    (embedded_selected_zero net f e p T hcomp h) (embedded_outside_negative net f e p T hcomp h)

theorem embeddedLocalizedModel_feeding_original (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (j : Fin h₁) (hj : (embeddedLocalizedModel net f e p T).Feeding j) : net.Feeding j :=
  net.localize_feeding_original _ f j hj

theorem embeddedLocalizedModel_support_cost_le (net : NormalizedNetwork N h₁ h₂)
    (f : Fin r ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (cost : ℕ→ℕ) :
    (∑ j,if 3≤(NormalizedNetwork.rowSupport ((embeddedLocalizedModel net f e p T).A j)).card
      then cost (NormalizedNetwork.rowSupport ((embeddedLocalizedModel net f e p T).A j)).card else 0)≤
    ∑ j,if 3≤(NormalizedNetwork.rowSupport (net.A j)).card ∧
      NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f
      then cost (NormalizedNetwork.rowSupport (net.A j)).card else 0 := by
  classical
  exact NormalizedNetwork.indexed_support_cost_le_of_masked_restriction f net.A
    (embeddedLocalizedModel net f e p T).A
    (fun j => NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f) cost
    (fun _ hj => hj) (embeddedLocalizedModel_A net f e p T hcomp h)
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
