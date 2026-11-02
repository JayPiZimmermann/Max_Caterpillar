import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 509, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0509
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .zero, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-4,-102,-102,-112⟩
        ) else (
          ⟨-8,-30,-30,-20⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-33,-27,-33,-36⟩
        ) else (
          ⟨31,31,37,26⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨-33,-33,-27,-36⟩
        ) else (
          ⟨31,37,31,26⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨28,40,40,20⟩
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
          ⟨-28,-40,-40,-20⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-31,-37,-31,-26⟩
        ) else (
          ⟨57,-15,-21,12⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-31,-31,-37,-26⟩
        ) else (
          ⟨57,-21,-15,12⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨8,30,30,20⟩
        ) else (
          ⟨52,102,102,160⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0509
