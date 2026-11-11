import research.sN.overnight_20261103.degree_two.GlobalComponents

/-! The component obstruction only needs braid forms on rows which feed an
original second unit. Arbitrary output-only first rows are allowed for free. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N h₁ h₂ : ℕ}

/-- Mask for one original unit, retaining all original index types. -/
def feedingMask (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) :
    NormalizedNetwork N h₁ h₂ :=
  {net with A := fun j => if net.W k j=0 then 0 else net.A j}

lemma feedingMask_normalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) :
    (feedingMask net k).TranslationNormalized := by
  refine ⟨?_,hn.2.1,hn.2.2⟩
  intro j
  by_cases hj : net.W k j=0
  · simp [feedingMask,hj]
  · simpa [feedingMask,hj] using hn.1 j

lemma feedingMask_braid (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (hb : ∀ j,net.W k j≠0 → (rowSupport (net.A j)).card≤2) :
    ∀ j,(rowSupport ((feedingMask net k).A j)).card≤2 := by
  intro j
  by_cases hj : net.W k j=0
  · norm_num [feedingMask,hj,rowSupport]
  · simpa [feedingMask,hj] using hb j hj

lemma feedingMask_inner (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (x : Point N) : (feedingMask net k).inner k x=net.inner k x := by
  unfold NormalizedNetwork.inner feedingMask
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : net.W k j=0 <;> simp [hj]

lemma feedingMask_edgeWeight (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (a b : Fin N) :
    braidEdgeWeight (feedingMask net k).A ((feedingMask net k).W k) a b=
      braidEdgeWeight net.A (net.W k) a b := by
  classical
  unfold braidEdgeWeight braidEdgeRows
  rw [Finset.sum_filter,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : net.W k j=0 <;> simp [feedingMask,hj]

lemma feedingMask_graph (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) :
    braidInteractionGraph (feedingMask net k) (feedingMask_normalized net hn k) k=
      braidInteractionGraph net hn k := by
  apply SimpleGraph.ext
  funext a b
  simp only [braidInteractionGraph_adj,feedingMask_edgeWeight]

lemma exists_inner_period_of_many_components_feeding
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (k : Fin h₂)
    (hb : ∀ j,net.W k j≠0 → (rowSupport (net.A j)).card≤2)
    (hc : 2<Nat.card (braidInteractionGraph net hn k).ConnectedComponent) :
    ∃ v : Point N,(∃ i j,v i≠v j) ∧ ∀ x,net.inner k (x+v)=net.inner k x := by
  let masked := feedingMask net k
  have hnorm := feedingMask_normalized net hn k
  have hcard := feedingMask_braid net k hb
  have hcomp : 2<Nat.card (braidInteractionGraph masked hnorm k).ConnectedComponent := by
    rwa [feedingMask_graph net hn k]
  obtain ⟨v,hv,hnd,hconst⟩ := exists_component_constant_kernel
    (braidInteractionGraph masked hnorm k) hcomp
    (ExponentialPush.ActualBraid.head (masked.U k) masked.A (masked.W k))
  refine ⟨v,hnd,?_⟩
  intro x
  have hp := inner_period_of_components masked hnorm hcard k v hv hconst x
  simpa only [masked,feedingMask_inner] using hp

/-- No width or direction restriction on output-only first neurons. -/
theorem exists_active_second_two_components_feeding [NeZero N] (hN : 3≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hbraid : ∀ k j,net.W k j≠0 → (rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum N x) :
    ∃ k : Fin h₂,net.d k≠0 ∧
      Nat.card (braidInteractionGraph net hn k).ConnectedComponent≤2 := by
  classical
  by_contra! hbad
  have hN2 : 2≤N := (by norm_num : 2≤3).trans hN
  have hscalar : FiniteDimensional.finrank ℝ ℝ≤N-2 := by
    rw [FiniteDimensional.finrank_self]
    exact (Nat.le_sub_iff_add_le hN2).mpr hN
  let f : Fin h₁ ⊕ Fin h₂ → Point N → ℝ :=
    Sum.elim (fun j x => net.B j*relu (lin (net.A j) x))
      (fun k x => net.d k*relu (net.inner k x))
  have hf : ∀ s,∃ v : Point N,(∃ i j,v i≠v j) ∧ ∀ x,f s (x+v)=f s x := by
    intro s
    rcases s with j|k
    · obtain ⟨v,hv,hnd⟩ := ExponentialPush.Ridge.exists_nondiagonal_ker_of_finrank
        hN2 (linMap (net.A j)) hscalar
      change lin (net.A j) v=0 at hv
      refine ⟨v,hnd,?_⟩
      intro x
      change net.B j*relu (lin (net.A j) (x+v))=net.B j*relu (lin (net.A j) x)
      rw [lin_add_right,hv,add_zero]
    · by_cases hd : net.d k=0
      · obtain ⟨v,_,hnd⟩ := ExponentialPush.Ridge.exists_nondiagonal_ker_of_finrank
          hN2 (0 : Point N →ₗ[ℝ] ℝ) hscalar
        refine ⟨v,hnd,?_⟩
        intro x
        change net.d k*relu (net.inner k (x+v))=net.d k*relu (net.inner k x)
        simp only [hd,zero_mul]
      · obtain ⟨v,hnd,hp⟩ := exists_inner_period_of_many_components_feeding
          net hn k (hbraid k) (hbad k hd)
        refine ⟨v,hnd,?_⟩
        intro x
        change net.d k*relu (net.inner k (x+v))=net.d k*relu (net.inner k x)
        rw [hp x]
  apply ExponentialPush.Ridge.maximum_ne_affine_sum_of_exists_periods hN2 f hf
    (linMap net.L).toAddMonoidHom 0
  intro x
  rw [←hmax x]
  simp only [f,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,eval,
    AddMonoidHom.coe_coe,add_zero]
  change lin net.L x+(∑ j,net.B j*relu (lin (net.A j) x))+
      ∑ k,net.d k*relu (net.inner k x)=
    lin net.L x+((∑ j,net.B j*relu (lin (net.A j) x))+
      ∑ k,net.d k*relu (net.inner k x))
  ring

#print axioms feedingMask_graph
#print axioms exists_inner_period_of_many_components_feeding
#print axioms exists_active_second_two_components_feeding
end MaxCaterpillar.Overnight.DegreeTwo
