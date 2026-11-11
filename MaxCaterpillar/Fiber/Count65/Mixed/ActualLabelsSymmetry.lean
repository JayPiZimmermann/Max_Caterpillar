import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsContinuity

/-! # Actual mixed component labels forget only physical second-row names -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function

def permutePhysical (q : Equiv.Perm (Fin 5)) (p : Slice) : Slice :=
  ⟨(p.val.1,permuteHidden p.val.2 (Equiv.refl _) q),p.property.1,p.property.2.1,
    (fun x => (permuteHidden_eval p.val.2 (Equiv.refl _) q x).trans
      (p.property.2.2.1 x)),(fun i => p.property.2.2.2 (q i))⟩

lemma continuous_permutePhysical (q : Equiv.Perm (Fin 5)) :
    Continuous (permutePhysical q) :=
  ((continuous_fst.comp continuous_subtype_val).prod_mk
    ((continuous_permuteHidden (Equiv.refl _) q).comp
      (continuous_snd.comp continuous_subtype_val))).subtype_mk _

def transportLabel (q : Equiv.Perm (Fin 5)) (l : Label) : Label :=
  ((rowOrder l).trans q.symm,l.2)

lemma permutePhysical_mem_class (q : Equiv.Perm (Fin 5)) (p : Slice) (l : Label) :
    permutePhysical q p ∈ physicalClass (transportLabel q l) ↔ p ∈ physicalClass l := by
  simp only [physicalClass,Set.mem_inter_iff,outputClass,stationaryClass,
    orientationClass,directionClass,headClass,Set.mem_setOf_eq,parameter,core,
    intercept,coeff,output,time,rowOrder,branch,orientations,signed,transportLabel,
    permutePhysical,permuteHidden,Equiv.trans_apply,Equiv.refl_apply,
    Equiv.apply_symm_apply]

lemma actualLabel_permutePhysical (q : Equiv.Perm (Fin 5)) (p : Slice) :
    actualLabel (permutePhysical q p)=transportLabel q (actualLabel p) :=
  (actualLabel_eq_iff _ _).mpr
    ((permutePhysical_mem_class q p (actualLabel p)).mpr (actualLabel_mem p))

/-- Forgetting physical row names is invariant under the actual allowed hidden
permutation, rather than identifying equal realized functions by definition. -/
theorem componentLabel_permutePhysical (q : Equiv.Perm (Fin 5)) (p : Slice) :
    componentLabel (permutePhysical q p)=componentLabel p := by
  unfold componentLabel
  rw [actualLabel_permutePhysical]
  rfl

#print axioms componentLabel_permutePhysical
end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
