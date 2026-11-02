import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 613, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0613
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-99,-87,-204,-111⟩
        ) else (
          ⟨-44,-48,-40,-42⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-20,4,10,-10⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨23,41,36,33⟩
        ) else (
          ⟨8,18,20,8⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨-12,-18,-10,-20⟩
        ) else (
          ⟨-36,-42,-64,-38⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨42,42,70,44⟩
        ) else (
          ⟨12,18,10,20⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-8,-18,-20,-8⟩
        ) else (
          ⟨-17,-41,-30,-27⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨20,12,6,10⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨44,48,40,42⟩
        ) else (
          ⟨83,75,176,95⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0613
