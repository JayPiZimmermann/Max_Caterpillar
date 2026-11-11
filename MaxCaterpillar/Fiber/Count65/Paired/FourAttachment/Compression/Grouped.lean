import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Compression.Roles
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.OffsetPath

/-! Physical compression of four local slots by their actual incoming rows. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m : ℕ}

noncomputable def groupTotal (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4)
    (a : Fin 4) : ℝ := ∑ i, if group i=a then j i else 0

lemma groupTotal_ne_zero_has_member (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4)
    (a : Fin 4) (ha : groupTotal j group a≠0) : ∃ i,group i=a := by
  classical
  by_contra h
  apply ha
  apply Finset.sum_eq_zero
  intro i _
  simp only [not_exists] at h
  simp [h i]

lemma groupTotal_sum (j f : Fin 4 → ℝ) (group : Fin 4 → Fin 4) :
    (∑ a,groupTotal j group a*f a)=∑ i,j i*f (group i) := by
  classical
  simp only [groupTotal,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]

noncomputable def fourGroupedNet (A : Fin m → Point N) (β g : Fin m → ℝ)
    (R : Fin 4 → Fin m → ℝ) (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4) :
    Network N m 5 where
  W₁ := A
  b₁ := β
  W₂ := Fin.cons g (fun i => R (group i))
  b₂ := 0
  w₃ := Fin.cons 1 j
  b₃ := 0

noncomputable def fourGroupedTarget (A : Fin m → Point N) (β g : Fin m → ℝ)
    (R : Fin 4 → Fin m → ℝ) (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4)
    (e : Equiv.Perm (Fin 4)) : Network N m 5 where
  W₁ := A
  b₁ := β
  W₂ := Fin.cons g (fun i => R (e.symm i))
  b₂ := 0
  w₃ := Fin.cons 1 (fun i => groupTotal j group (e.symm i))
  b₃ := 0

/-- One readout interpolation merges all four groups simultaneously; a second
incoming-row interpolation repurposes each slot assigned to an empty group. -/
theorem fourGrouped_compress [NeZero N]
    (A : Fin m → Point N) (β g : Fin m → ℝ)
    (R : Fin 4 → Fin m → ℝ) (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4)
    (hexact : ∀ x,(fourGroupedNet A β g R j group).eval x=Maximum N x) :
    ∃ e : Equiv.Perm (Fin 4),
      JoinedIn (ExactSet N m 5) (fourGroupedNet A β g R j group)
        (fourGroupedTarget A β g R j group e) := by
  classical
  obtain ⟨e,he⟩ := fourGroup_roles group
  let source := fourGroupedNet A β g R j group
  let target := fourGroupedTarget A β g R j group e
  let merged := withOutput source target.w₃ 0
  have hrow : ∀ k,merged.w₃ k≠0 → ∀ x,
      preact merged.W₁ merged.b₁ (target.W₂ k) (target.b₂ k) x=
        preact merged.W₁ merged.b₁ (merged.W₂ k) (merged.b₂ k) x := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · intro _ x
      rfl
    · intro hk x
      change preact A β (R (e.symm i)) 0 x=preact A β (R (group i)) 0 x
      have hn : groupTotal j group (e.symm i)≠0 := hk
      have hh := he (e.symm i) (groupTotal_ne_zero_has_member j group _ hn)
      rw [e.apply_symm_apply] at hh
      rw [hh]
  have hmerged : ∀ x,merged.eval x=source.eval x := by
    intro x
    rw [Network.eval,Fin.sum_univ_succ]
    simp only [merged,source,target,withOutput,fourGroupedNet,fourGroupedTarget,
      Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,one_mul]
    change relu (preact A β g 0 x)+
      (∑ i,groupTotal j group (e.symm i)*relu (preact A β (R (group i)) 0 x))+0=
        source.eval x
    have hlocal : (∑ i,groupTotal j group (e.symm i)*
        relu (preact A β (R (group i)) 0 x))=
      ∑ i,j i*relu (preact A β (R (group i)) 0 x) := by
      calc
        _ = ∑ i,groupTotal j group (e.symm i)*
            relu (preact A β (R (e.symm i)) 0 x) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : groupTotal j group (e.symm i)=0
          · simp only [hi,zero_mul]
          · have hh := he (e.symm i) (groupTotal_ne_zero_has_member j group _ hi)
            rw [e.apply_symm_apply] at hh
            rw [hh]
        _ = ∑ a,groupTotal j group a*relu (preact A β (R a) 0 x) :=
          Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
        _ = _ := groupTotal_sum j (fun a => relu (preact A β (R a) 0 x)) group
    rw [hlocal]
    simp only [source,fourGroupedNet,Network.eval,Fin.sum_univ_succ,
      Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,one_mul,add_zero,preact]
  have hp : JoinedIn (ExactSet N m 5) source merged := by
    apply JoinedIn.ofLine (continuous_interpolateOutput source target.w₃ 0).continuousOn
      (interpolateOutput_zero _ _ _) (interpolateOutput_one _ _ _)
    rintro _ ⟨t,_,rfl⟩ x
    rw [interpolateOutput_eval,hmerged x]
    have hh := hexact x
    change source.eval x=Maximum N x at hh
    rw [hh]
    ring
  have hr : JoinedIn (ExactSet N m 5) merged target := by
    have hend : withSecondRows merged target.W₂ target.b₂=target := by rfl
    rw [← hend]
    apply JoinedIn.ofLine
      (continuous_interpolateSecondRows merged target.W₂ target.b₂).continuousOn
      (interpolateSecondRows_zero _ _ _) (interpolateSecondRows_one _ _ _)
    rintro _ ⟨t,_,rfl⟩ x
    rw [interpolateSecondRows_eval merged target.W₂ target.b₂ hrow t x,hmerged x]
    exact hexact x
  exact ⟨e,hp.trans hr⟩

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
