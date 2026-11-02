import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 493, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0493
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .zero, .neg, .neg, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-56,-52,-52,-52⟩
        ) else (
          ⟨-20,16,16,20⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨36,-28,84,40⟩
        ) else (
          ⟨40,38,6,20⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨36,84,-28,40⟩
        ) else (
          ⟨40,6,38,20⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨-16,2,2,-16⟩
        ) else (
          ⟨-60,-60,-60,-60⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨60,60,60,60⟩
        ) else (
          ⟨16,-2,-2,16⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-40,-6,-38,-20⟩
        ) else (
          ⟨-36,-78,12,-50⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-40,-38,-6,-20⟩
        ) else (
          ⟨-36,12,-78,-50⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨20,-10,-10,-8⟩
        ) else (
          ⟨56,52,52,52⟩
        )
      )
    )
  )
def psi (P : Fin 16) : IntegerForm 4 := (psiQuad P).toForm

theorem fast_check : integerQuadTableCheck
    (fun P => compiledMaskedPsiQuad 15 P pattern) psiQuad = true := by
  kernel_bool_check

theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients 15 P pattern i = psi P i := by
  rw [← compiledMaskedPsiQuad_toForm]
  exact congrArg (fun q : IntegerQuad => q.toForm i)
    (integerQuadTableCheck_sound _ _ fast_check P)

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0493
