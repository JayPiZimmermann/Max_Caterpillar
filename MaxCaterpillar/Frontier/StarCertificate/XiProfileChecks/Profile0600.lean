import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 600, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0600
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-4,-4,0,-40⟩
        ) else (
          ⟨-20,-52,-30,-18⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-52,-20,-30,-18⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨10,10,16,44⟩
        ) else (
          ⟨0,32,14,0⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨32,0,14,0⟩
        ) else (
          ⟨-42,-42,-44,-44⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨42,42,44,44⟩
        ) else (
          ⟨-38,-6,-14,-6⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-6,-38,-14,-6⟩
        ) else (
          ⟨-10,-10,-16,-44⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨46,14,30,12⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨14,46,30,12⟩
        ) else (
          ⟨-16,-16,0,20⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0600
