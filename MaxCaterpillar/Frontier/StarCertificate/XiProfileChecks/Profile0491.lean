import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 491, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0491
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-32,-32,-36,-40⟩
        ) else (
          ⟨4,-6,-2,4⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-6,4,-2,4⟩
        ) else (
          ⟨34,34,40,32⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨6,6,16,12⟩
        ) else (
          ⟨22,32,22,24⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨32,22,22,24⟩
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
          ⟨-32,-22,-22,-24⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-22,-32,-22,-24⟩
        ) else (
          ⟨-6,-6,-16,-12⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-34,-34,-40,-32⟩
        ) else (
          ⟨6,-4,2,-4⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨-4,6,2,-4⟩
        ) else (
          ⟨32,32,36,40⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0491
