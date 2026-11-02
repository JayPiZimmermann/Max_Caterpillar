import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

lemma permutationHomeomorph_sameQuotient (p : Equiv.Perm (Fin 6))
    (q : Equiv.Perm (Fin 4)) (x : ExactFiber 4 6 5) :
    quotientMk (Mixed65.permutationHomeomorph p q x)=quotientMk x := by
  exact (quotientMk_eq_of_step (SymmetryStep.input
    (permuteHiddenFiber p (Equiv.refl _) x) q)).symm.trans
    (quotientMk_eq_of_step (SymmetryStep.hidden x p (Equiv.refl _))).symm

lemma permutationHomeomorph_symm_sameQuotient (p : Equiv.Perm (Fin 6))
    (q : Equiv.Perm (Fin 4)) (x : ExactFiber 4 6 5) :
    quotientMk ((Mixed65.permutationHomeomorph p q).symm x)=quotientMk x := by
  have h := permutationHomeomorph_sameQuotient p q
    ((Mixed65.permutationHomeomorph p q).symm x)
  rw [(Mixed65.permutationHomeomorph p q).apply_symm_apply] at h
  exact h.symm

end MaxCaterpillar.Fiber.Count65.SectorQuotient
