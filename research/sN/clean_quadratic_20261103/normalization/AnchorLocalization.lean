import research.sN.clean_quadratic_20261103.normalization.AnchorLift
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Localization

/-! One localization suffices when selected directions preserve the diagonal.
Both original hidden-layer index types are retained. -/
set_option autoImplicit false
namespace MaxCaterpillar.CleanQuadratic.Normalization
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N m h₁ h₂ : ℕ}

private theorem sum_firstLinear_refl (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i,net.A j i=0) (q : Point N) (c : Fin h₁ → ℝ) :
    (∑ i,net.firstLinear q (Function.Embedding.refl _) c i)=0 := by
  have hh : lin (net.firstLinear q (Function.Embedding.refl _) c) (diag 1)=0 := by
    rw [firstLinear,lin_sum_left]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : 0<lin (net.A j) q
    · rw [if_pos hj,lin_smul_left]
      change c j * lin (net.A j) (diag 1)=0
      rw [lin_diag,hA j,mul_zero,mul_zero]
    · rw [if_neg hj,lin_zero_left]
  simpa only [lin_diag,one_mul] using hh

theorem localFirst_refl_normalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (q : Point N) :
    (net.localFirst q (Function.Embedding.refl _)).TranslationNormalized := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro j
    change (∑ i,(if lin (net.A j) q=0 then restrict (Function.Embedding.refl _) (net.A j)
      else (0 : Point N)) i)=0
    by_cases hj : lin (net.A j) q=0
    · simpa [hj,restrict] using hn.1 j
    · simp [hj]
  · intro k
    change (∑ i,(restrict (Function.Embedding.refl _) (net.U k)+
      net.firstLinear q (Function.Embedding.refl _) (net.W k)) i)=0
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    change (∑ i,net.U k i)+(∑ i,net.firstLinear q (Function.Embedding.refl _) (net.W k) i)=0
    rw [hn.2.1 k,sum_firstLinear_refl net hn.1,add_zero]
  · change (∑ i,(restrict (Function.Embedding.refl _) net.L+
      net.firstLinear q (Function.Embedding.refl _) net.B) i)=1
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    change (∑ i,net.L i)+(∑ i,net.firstLinear q (Function.Embedding.refl _) net.B i)=1
    rw [hn.2.2,sum_firstLinear_refl net hn.1,add_zero]

theorem freezeOuter_normalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (β : Fin h₂ → ℝ) :
    (freezeOuter net β).TranslationNormalized := by
  classical
  refine ⟨hn.1,?_,?_⟩
  · intro k
    change (∑ i,(if β k=0 then net.U k else (0 : Point N)) i)=0
    by_cases hk : β k=0
    · simpa [hk] using hn.2.1 k
    · simp [hk]
  · have hs : lin (∑ k,if 0<β k then net.d k • net.U k else 0) (diag 1)=0 := by
      rw [lin_sum_left]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : 0<β k
      · rw [if_pos hk,lin_smul_left,lin_diag,hn.2.1 k,mul_zero,mul_zero]
      · rw [if_neg hk,lin_zero_left]
    have hh : lin (freezeOuter net β).L (diag 1)=1 := by
      change lin (net.L+∑ k,if 0<β k then net.d k • net.U k else 0) (diag 1)=1
      rw [lin_add_left,hs,lin_diag,hn.2.2,one_mul,add_zero]
    simpa only [lin_diag,one_mul] using hh

theorem localize_refl_normalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (q : Point N) :
    (net.localize q (Function.Embedding.refl _)).TranslationNormalized :=
  freezeOuter_normalized _ (localFirst_refl_normalized net hn q) _

noncomputable def anchorPullback (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (a : Fin m) : NormalizedNetwork m h₁ h₂ where
  A j := anchorRestrict e a (net.A j)
  U k := anchorRestrict e a (net.U k)
  W := net.W
  L := anchorRestrict e a net.L
  B := net.B
  d := net.d

theorem anchorPullback_eval (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (a : Fin m) (x : Point m) :
    (anchorPullback net e a).eval x = net.eval (anchorLift e a x) := by
  simp only [eval,NormalizedNetwork.inner,anchorPullback,←lin_anchorLift]

theorem anchorPullback_normalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (e : Fin m ↪ Fin N) (a : Fin m) :
    (anchorPullback net e a).TranslationNormalized := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact (sum_anchorRestrict e a (net.A j)).trans (hn.1 j)
  · intro k
    exact (sum_anchorRestrict e a (net.U k)).trans (hn.2.1 k)
  · exact (sum_anchorRestrict e a net.L).trans hn.2.2

noncomputable def anchorLocalize (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (a : Fin m) : NormalizedNetwork m h₁ h₂ :=
  anchorPullback (net.localize q (Function.Embedding.refl _)) e a

theorem anchorLocalize_normalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (q : Point N) (e : Fin m ↪ Fin N) (a : Fin m) :
    (anchorLocalize net q e a).TranslationNormalized :=
  anchorPullback_normalized _ (localize_refl_normalized net hn q) e a

theorem anchorLocalize_computes_max [NeZero N] [NeZero m]
    (net : NormalizedNetwork N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x)
    (e : Fin m ↪ Fin N) (a : Fin m) (q : Point N)
    (hq : ∀ i,q (e i)=0)
    (hneg : ∀ i,i∉Finset.univ.image e → q i<0) :
    ∀ x,(anchorLocalize net q e a).eval x=Maximum m x := by
  intro x
  obtain ⟨ε,hε,he⟩ := net.exists_eval_direction q (Function.Embedding.refl _) (anchorLift e a x)
  have hlift : lift (Function.Embedding.refl _) (anchorLift e a x)=anchorLift e a x := by
    ext i
    exact lift_selected _ _ i
  rw [hlift,hnet,hnet,tied_Maximum_zero e q hq hneg,zero_add,
    maximum_anchorLift e a q hq hneg x ε hε] at he
  change (anchorPullback (net.localize q (Function.Embedding.refl _)) e a).eval x=_
  rw [anchorPullback_eval,localize_eval]
  exact mul_left_cancel₀ hε.ne' he.symm

theorem anchorLocalize_first_row (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (a : Fin m)
    (hzero : ∀ j,lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image e)
    (j : Fin h₁) :
    (anchorLocalize net q e a).A j =
      if rowSupport (net.A j)⊆Finset.univ.image e then restrict e (net.A j) else 0 := by
  classical
  change anchorRestrict e a ((net.localize q (Function.Embedding.refl _)).A j)=_
  rw [localize_first_row]
  by_cases hj : rowSupport (net.A j)⊆Finset.univ.image e
  · rw [if_pos ((hzero j).mpr hj),if_pos hj]
    exact anchorRestrict_of_support e a (net.A j) hj
  · rw [if_neg (fun h => hj ((hzero j).mp h)),if_neg hj,anchorRestrict_zero]

/-- Full actual-model restriction using one localization. No second diagonal
normalization is applied, and neither hidden-layer index type is changed. -/
theorem exists_anchor_localized [NeZero N] [NeZero m]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) (e : Fin m ↪ Fin N) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x,model.eval x=Maximum m x) ∧ model.TranslationNormalized ∧
      (∀ j,model.A j = if rowSupport (net.A j)⊆Finset.univ.image e
        then restrict e (net.A j) else 0) := by
  classical
  obtain ⟨q,hq,hneg,hzero⟩ := net.exists_generic_tied_point e
  exact ⟨anchorLocalize net q e 0,
    anchorLocalize_computes_max net hnet e 0 q hq hneg,
    anchorLocalize_normalized net hn q e 0,
    anchorLocalize_first_row net q e 0 hzero⟩

#check @exists_anchor_localized
#print axioms anchorLocalize_computes_max
#print axioms anchorLocalize_normalized
#print axioms anchorLocalize_first_row
#print axioms exists_anchor_localized
end MaxCaterpillar.CleanQuadratic.Normalization
