import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 587, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0587
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-4,-8,-12,-16⟩
        ) else (
          ⟨-28,-36,-30,-26⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-28,-16,-18,-18⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨26,30,28,36⟩
        ) else (
          ⟨6,14,14,6⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨6,-6,2,-2⟩
        ) else (
          ⟨-38,-38,-44,-40⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨38,38,44,40⟩
        ) else (
          ⟨-6,6,-2,2⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-6,-14,-14,-6⟩
        ) else (
          ⟨-26,-30,-28,-36⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨28,16,18,18⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨28,36,30,26⟩
        ) else (
          ⟨4,8,12,16⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0587
