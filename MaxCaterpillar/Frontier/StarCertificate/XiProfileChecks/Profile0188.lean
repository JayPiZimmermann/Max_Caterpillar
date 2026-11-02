import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 188, mask 11. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0188
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .zero, .zero, .zero, .zero, .pos, .pos, .pos, .zero, .zero, .zero, .zero, .zero]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨30,30,0,-8⟩
        ) else (
          ⟨-24,-58,0,-22⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-58,-24,0,-22⟩
        ) else (
          ⟨60,60,0,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨-30,-30,0,8⟩
        ) else (
          ⟨16,50,0,14⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨50,16,0,14⟩
        ) else (
          ⟨-60,-60,0,-60⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨60,60,0,60⟩
        ) else (
          ⟨-56,-22,0,-20⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-22,-56,0,-20⟩
        ) else (
          ⟨30,30,0,-8⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,0,-60⟩
        ) else (
          ⟨34,0,0,-2⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨0,34,0,-2⟩
        ) else (
          ⟨-30,-30,0,8⟩
        )
      )
    )
  )
def psi (P : Fin 16) : IntegerForm 4 := (psiQuad P).toForm

theorem fast_check : integerQuadTableCheck
    (fun P => compiledMaskedPsiQuad 11 P pattern) psiQuad = true := by
  kernel_bool_check

theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients 11 P pattern i = psi P i := by
  rw [← compiledMaskedPsiQuad_toForm]
  exact congrArg (fun q : IntegerQuad => q.toForm i)
    (integerQuadTableCheck_sound _ _ fast_check P)

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0188
