import MaxCaterpillar.Fiber.Count65.Star.ActualLabelsNormalization

/-! # Star labels respect genuine second hidden permutations

The action below permutes every incident physical coefficient and bias. The
32-valued label forgets only the names of the five physical rows.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 PhysicalExtraction MaxCaterpillar.Frontier

noncomputable def permuteNormalized (p : Slice) (q : Equiv.Perm (Fin 5)) : Slice :=
  ⟨(p.val.1,permuteHidden p.val.2 (Equiv.refl _) q),p.property.1,p.property.2.1,
    p.property.2.2.1,
    (fun x => (permuteHidden_eval p.val.2 (Equiv.refl _) q x).trans (p.property.2.2.2.1 x)),
    fun i => p.property.2.2.2.2 (q i)⟩
noncomputable def permutePhysical (p : RawSlice) (q : Equiv.Perm (Fin 5)) : RawSlice :=
  ⟨(p.val.1,permuteHidden p.val.2 (Equiv.refl _) q),p.property.1,p.property.2.1,
    p.property.2.2.1,
    fun x => (permuteHidden_eval p.val.2 (Equiv.refl _) q x).trans (p.property.2.2.2 x)⟩

/-- Row names are transported contravariantly by the physical permutation. -/
noncomputable def permuteLabel (l : Label) (q : Equiv.Perm (Fin 5)) : Label :=
  ((rowOrder l).trans q.symm,l.2)

lemma physicalClass_permuteNormalized (p : Slice) (q : Equiv.Perm (Fin 5))
    (l : Label) (h : p ∈ physicalClass l) :
    permuteNormalized p q ∈ physicalClass (permuteLabel l q) := by
  simpa [physicalClass,outputClass,stationaryClass,orientationClass,directionClass,
    carrierClass,branchClass,headClass,core,hValue,kValue,nValue,mValue,lValue,
    normalizedCoeff,intercept,coeff,output,time,permuteNormalized,permuteLabel,
    rowOrder,branch,orientations,signed,permuteHidden,Equiv.trans_apply] using h

/-- The finite physical row ordering changes by the actual permutation. -/
theorem actualLabel_permuteNormalized (p : Slice) (q : Equiv.Perm (Fin 5)) :
    actualLabel (permuteNormalized p q)=permuteLabel (actualLabel p) q :=
  (actualLabel_eq_iff _ _).mpr
    (physicalClass_permuteNormalized p q (actualLabel p) (actualLabel_mem p))

/-- Branch, orientations and head type are invariant under physical row names. -/
theorem componentLabel_permuteNormalized (p : Slice) (q : Equiv.Perm (Fin 5)) :
    componentLabel (permuteNormalized p q)=componentLabel p := by
  unfold componentLabel
  rw [actualLabel_permuteNormalized]
  rfl

theorem componentLabel32_permuteNormalized (p : Slice) (q : Equiv.Perm (Fin 5)) :
    componentLabel32 (permuteNormalized p q)=componentLabel32 p := by
  unfold componentLabel32
  rw [componentLabel_permuteNormalized]

lemma normalizeSecond_permuteHidden {N h₁ h₂ : ℕ}
    (net : Network N h₁ h₂) (p : Equiv.Perm (Fin h₁)) (q : Equiv.Perm (Fin h₂)) :
    normalizeSecond (permuteHidden net p q)=permuteHidden (normalizeSecond net) p q := rfl

lemma normalizePhysical_permutePhysical (p : RawSlice) (q : Equiv.Perm (Fin 5)) :
    normalizePhysical (permutePhysical p q)=permuteNormalized (normalizePhysical p) q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact normalizeSecond_permuteHidden p.val.2 (Equiv.refl _) q

theorem rawComponentLabel_permutePhysical (p : RawSlice) (q : Equiv.Perm (Fin 5)) :
    rawComponentLabel (permutePhysical p q)=rawComponentLabel p := by
  unfold rawComponentLabel
  rw [normalizePhysical_permutePhysical,componentLabel_permuteNormalized]

theorem rawComponentLabel32_permutePhysical (p : RawSlice) (q : Equiv.Perm (Fin 5)) :
    rawComponentLabel32 (permutePhysical p q)=rawComponentLabel32 p := by
  unfold rawComponentLabel32
  rw [normalizePhysical_permutePhysical,componentLabel32_permuteNormalized]

#print axioms physicalClass_permuteNormalized
#print axioms actualLabel_permuteNormalized
#print axioms componentLabel_permuteNormalized
#print axioms componentLabel32_permuteNormalized
#print axioms rawComponentLabel32_permutePhysical
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
