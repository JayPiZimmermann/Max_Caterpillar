import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 610, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0610
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-240,-376,-422,-422⟩
        ) else (
          ⟨-44,-52,-40,-40⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨4,24,10,10⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨32,32,46,14⟩
        ) else (
          ⟨60,14,88,10⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨12,2,62,0⟩
        ) else (
          ⟨-26,-32,-8,-40⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨32,32,14,46⟩
        ) else (
          ⟨60,14,10,88⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨12,2,0,62⟩
        ) else (
          ⟨-26,-32,-40,-8⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨-4,8,6,6⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨44,52,40,40⟩
        ) else (
          ⟨208,64,234,234⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0610
