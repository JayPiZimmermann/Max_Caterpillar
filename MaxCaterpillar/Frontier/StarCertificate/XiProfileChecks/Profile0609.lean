import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 609, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0609
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-28,-64,-30,-30⟩
        ) else (
          ⟨-52,-52,-48,-48⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨20,0,-10,-10⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨44,50,40,38⟩
        ) else (
          ⟨36,14,64,-38⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨-36,2,38,-48⟩
        ) else (
          ⟨-44,-50,-38,-40⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨44,50,38,40⟩
        ) else (
          ⟨36,14,-38,64⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-36,2,-48,38⟩
        ) else (
          ⟨-44,-50,-40,-38⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨-20,0,10,10⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨52,52,48,48⟩
        ) else (
          ⟨28,40,18,18⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0609
