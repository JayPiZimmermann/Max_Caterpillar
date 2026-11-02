import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 615, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0615
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .zero]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-6,-10,10,6⟩
        ) else (
          ⟨-46,-32,-50,-44⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-24,-26,-28,-38⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨38,28,26,24⟩
        ) else (
          ⟨12,46,46,12⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨-8,8,-8,8⟩
        ) else (
          ⟨-44,-50,-32,-46⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨44,50,32,46⟩
        ) else (
          ⟨8,-8,8,-8⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-12,-46,-46,-12⟩
        ) else (
          ⟨-38,-38,-36,-24⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨24,36,38,38⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨46,32,50,44⟩
        ) else (
          ⟨6,10,-10,-6⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0615
