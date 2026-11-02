import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile 583, mask 15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0583
open BigOperators

def pattern : Fin 15 → Sign := ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
def psiQuad (P : Fin 16) : IntegerQuad :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          ⟨-107,-105,-115,-222⟩
        ) else (
          ⟨-16,-34,-18,-6⟩
        )
      ) else (
        if P.val < 3 then (
          ⟨-20,4,-10,10⟩
        ) else (
          ⟨60,60,60,60⟩
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          ⟨42,42,44,70⟩
        ) else (
          ⟨12,18,20,10⟩
        )
      ) else (
        if P.val < 7 then (
          ⟨4,12,0,14⟩
        ) else (
          ⟨-35,-41,-41,-40⟩
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          ⟨41,41,47,46⟩
        ) else (
          ⟨-6,-2,-2,-6⟩
        )
      ) else (
        if P.val < 11 then (
          ⟨-12,-18,-20,-10⟩
        ) else (
          ⟨-36,-42,-38,-64⟩
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          ⟨-60,-60,-60,-60⟩
        ) else (
          ⟨20,12,10,6⟩
        )
      ) else (
        if P.val < 15 then (
          ⟨16,34,18,6⟩
        ) else (
          ⟨81,95,89,186⟩
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

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0583
