import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabels
import MaxCaterpillar.Fiber.Count65.Mixed.RoleUniqueness

/-! # Every actual normalized mixed physical network has a finite label

This is an exhaustive cover of the actual physical slice. Its hypotheses are
exact all-real Max4 evaluation, the actual first matrix, and unit output
normalization; no residual or head form is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function Mixed65 MaxCaterpillar.Frontier PhysicalExtraction

lemma normalizeSecond_eq_of_unit (net : Network 4 6 5)
    (hu : ∀ i, net.w₃ i=1 ∨ net.w₃ i = -1) : normalizeSecond net=net := by
  have habs (i : Fin 5) : |net.w₃ i|=1 := by
    rcases hu i with h | h <;> rw [h] <;> norm_num
  simp [normalizeSecond,scaleSecond,habs]

noncomputable def normalForm (p : Slice) : PhysicalNormalForm p.val.2 p.val.1 := by
  have h := exists_physical_normal_form p.val.2 p.val.1 p.property.1
    p.property.2.1 p.property.2.2.1
  rw [normalizeSecond_eq_of_unit p.val.2 p.property.2.2.2] at h
  exact Classical.choice h

lemma normalForm_mem_class (p : Slice) (r : PhysicalNormalForm p.val.2 p.val.1)
    (e : Equiv.Perm (Fin 5))
    (he : ∀ i : Fin 3, e (Fin.castAdd 2 i)=r.coreIndex i)
    (hp : e 3=r.positiveHead) (hn : e 4=r.negativeHead) :
    ∃ l : Label, rowOrder l=e ∧ p ∈ physicalClass l := by
  classical
  let bits : Fin 3 → Bool := fun i => decide ((r.core.reindex r.order).W i < 0)
  have hw (i : Fin 3) : (core p e).W i=eps bits i := by
    change p.val.2.W₂ (e (Fin.castAdd 2 i)) 2=eps bits i
    rw [he,← r.ordered_W]
    simpa [eps,bits] using r.orientations i
  have hU (i : Fin 3) : (core p e).U i=(r.core.reindex r.order).U i := by
    change p.val.2.W₂ (e (Fin.castAdd 2 i)) 0=_
    rw [he]; exact (r.ordered_U i).symm
  have hV (i : Fin 3) : (core p e).V i=(r.core.reindex r.order).V i := by
    change p.val.2.W₂ (e (Fin.castAdd 2 i)) 1=_
    rw [he]; exact (r.ordered_V i).symm
  have hW (i : Fin 3) : (core p e).W i=(r.core.reindex r.order).W i := by
    change p.val.2.W₂ (e (Fin.castAdd 2 i)) 2=_
    rw [he]; exact (r.ordered_W i).symm
  have hT (i : Fin 3) : (core p e).T i=(r.core.reindex r.order).T i := by
    change p.val.2.W₂ (e (Fin.castAdd 2 i)) 3=_
    rw [he]; exact (r.ordered_T i).symm
  have hsquare (i : Fin 3) : eps bits i*eps bits i=1 := by
    unfold eps
    split_ifs <;> norm_num
  have houtput : ∀ b s : Bool, p ∈ outputClass (e,b,bits,s) := by
    intro b s i
    change p.val.2.w₃ (e i)=outputPattern i
    fin_cases i
    · change p.val.2.w₃ (e 0)=1
      rw [show e 0=r.coreIndex 0 from he 0]
      exact r.core_output_zero
    · change p.val.2.w₃ (e 1)=1
      rw [show e 1=r.coreIndex 1 from he 1]
      exact r.core_output_one
    · change p.val.2.w₃ (e 2) = -1
      rw [show e 2=r.coreIndex 2 from he 2]
      exact r.core_output_two
    · change p.val.2.w₃ (e 3)=1
      rw [hp]
      exact r.positive_output
    · change p.val.2.w₃ (e 4) = -1
      rw [hn]
      exact r.negative_output
  have hstationary : ∀ b s : Bool, p ∈ stationaryClass (e,b,bits,s) := by
    intro b s i
    change p.val.2.W₂ (e (Fin.castAdd 2 i)) 4=0 ∧
      p.val.2.W₂ (e (Fin.castAdd 2 i)) 5=0
    rw [he]
    exact r.core_stationary i
  have horient : ∀ b s : Bool, p ∈ orientationClass (e,b,bits,s) :=
    fun _ _ => hw
  have hdir : ∃ b : Bool, ∀ s : Bool, p ∈ directionClass (e,b,bits,s) := by
    rcases r.branches with ⟨k,hk,hd⟩ | ⟨v,hv,hd⟩
    · have hd' : (core p e).HasADirections (time p) k := by
        unfold ResidualSystem.HasADirections at hd ⊢
        simpa only [hU,hV,hW,hT,time] using hd
      have hepar : ∀ s : Bool, parameter (e,false,bits,s) p=k := by
        intro s
        change eps bits 1*coeff p (e 1) 3=k
        have hh := hd'.2.2.2.2.2.1
        change coeff p (e 1) 3=k*(core p e).W 1 at hh
        rw [hh,hw]
        calc
          eps bits 1*(k*eps bits 1)=k*(eps bits 1*eps bits 1) := by ring
          _ = k := by rw [hsquare]; ring
      refine ⟨false,?_⟩
      intro s
      change 1 ≤ time p*parameter (e,false,bits,s) p ∧ _
      rw [hepar s]
      exact ⟨hk,hd'⟩
    · have hd' : (core p e).HasBDirections (time p) v := by
        unfold ResidualSystem.HasBDirections at hd ⊢
        simpa only [hU,hV,hW,hT,time] using hd
      have hepar : ∀ s : Bool, parameter (e,true,bits,s) p=v := by
        intro s
        change eps bits 0*coeff p (e 0) 1=v
        have hh := hd'.2.1
        change coeff p (e 0) 1=v*(core p e).W 0 at hh
        rw [hh,hw]
        calc
          eps bits 0*(v*eps bits 0)=v*(eps bits 0*eps bits 0) := by ring
          _ = v := by rw [hsquare]; ring
      refine ⟨true,?_⟩
      intro s
      change 1+time p ≤ time p*parameter (e,true,bits,s) p ∧ _
      rw [hepar s]
      exact ⟨hv,hd'⟩
  have hhead : ∃ s : Bool, ∀ b : Bool, p ∈ headClass (e,b,bits,s) := by
    rcases r.head_kind with hs | hh
    · refine ⟨true,?_⟩
      intro b x
      change (actualHeads p.val.2 p.val.1 (e 3) (e 4)).A x+
        (actualHeads p.val.2 p.val.1 (e 3) (e 4)).B x=0
      rw [hp,hn,hs.1,hs.2.1]
      exact add_neg_self _
    · refine ⟨false,?_⟩
      intro b x
      change 0 ≤ (actualHeads p.val.2 p.val.1 (e 3) (e 4)).A x ∧
        0 ≤ (actualHeads p.val.2 p.val.1 (e 3) (e 4)).B x
      rw [hp,hn]
      exact ⟨hh.intercepts_nonneg.1 x,hh.intercepts_nonneg.2 x⟩
  obtain ⟨b,hb⟩ := hdir
  obtain ⟨s,hs⟩ := hhead
  exact ⟨(e,b,bits,s),rfl,⟨⟨⟨⟨houtput b s,hstationary b s⟩,horient b s⟩,hb s⟩,hs b⟩⟩

/-- Every actual normalized physical mixed network belongs to a finite
coefficient-defined class. All residual and head forms are conclusions. -/
theorem physicalClasses_exhaustive (p : Slice) : ∃ l : Label, p ∈ physicalClass l := by
  let r := normalForm p
  obtain ⟨l,_,hl⟩ := normalForm_mem_class p r r.roleOrder r.roleOrder_core
    r.roleOrder_positiveHead r.roleOrder_negativeHead
  exact ⟨l,hl⟩

#check @physicalClasses_exhaustive
#print axioms physicalClasses_exhaustive

end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
