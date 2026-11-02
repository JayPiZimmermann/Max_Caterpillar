import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 574, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0574
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-16,0,-32,-32⟩
        ) else (
          ⟨-16,-44,-10,-10⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-28,-22,-24,-24⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨38,42,44,72⟩
        ) else (
          ⟨-6,20,16,-12⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨6,4,36,8⟩
        ) else (
          ⟨-38,-36,-66,-38⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨38,42,72,44⟩
        ) else (
          ⟨-6,20,-12,16⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨6,4,8,36⟩
        ) else (
          ⟨-38,-36,-38,-66⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨28,-8,-6,-6⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨16,44,10,10⟩
        ) else (
          ⟨16,0,32,32⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0574
