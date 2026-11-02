import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 542, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0542
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-4,-4,-12,-40⟩
        ) else (
          ⟨-16,-46,-14,-12⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-46,-16,-14,-12⟩
        ) else (
          ⟨34,34,40,32⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨-54,-54,-8,-20⟩
        ) else (
          ⟨28,58,34,26⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨58,28,34,26⟩
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
          ⟨-64,-34,-34,-32⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-34,-64,-34,-32⟩
        ) else (
          ⟨54,54,8,20⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-34,-34,-40,-32⟩
        ) else (
          ⟨40,10,14,6⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨10,40,14,6⟩
        ) else (
          ⟨-16,-16,12,20⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0542
