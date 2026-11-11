import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask00
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask01
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask02
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask03
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask04
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask05
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask06
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask07
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask08
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask09
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask10
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask11
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask12
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask13
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask14
import MaxCaterpillar.Frontier.StarCertificate.XiCompiledSelectors.Checks.Mask15

/-! One balanced mask/permutation lookup supplies a whole literal selector row. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate

def compiledSelectorRow (T : Fin 16) (p : Fin 120) : CompiledSelectorRow :=
  if T.val < 8 then (
    if T.val < 4 then (
      if T.val < 2 then (
        if T.val < 1 then (
          CompiledSelectorData.row00 p
        ) else (
          CompiledSelectorData.row01 p
        )
      ) else (
        if T.val < 3 then (
          CompiledSelectorData.row02 p
        ) else (
          CompiledSelectorData.row03 p
        )
      )
    ) else (
      if T.val < 6 then (
        if T.val < 5 then (
          CompiledSelectorData.row04 p
        ) else (
          CompiledSelectorData.row05 p
        )
      ) else (
        if T.val < 7 then (
          CompiledSelectorData.row06 p
        ) else (
          CompiledSelectorData.row07 p
        )
      )
    )
  ) else (
    if T.val < 12 then (
      if T.val < 10 then (
        if T.val < 9 then (
          CompiledSelectorData.row08 p
        ) else (
          CompiledSelectorData.row09 p
        )
      ) else (
        if T.val < 11 then (
          CompiledSelectorData.row10 p
        ) else (
          CompiledSelectorData.row11 p
        )
      )
    ) else (
      if T.val < 14 then (
        if T.val < 13 then (
          CompiledSelectorData.row12 p
        ) else (
          CompiledSelectorData.row13 p
        )
      ) else (
        if T.val < 15 then (
          CompiledSelectorData.row14 p
        ) else (
          CompiledSelectorData.row15 p
        )
      )
    )
  )

theorem compiledSelectorRow_valid (T : Fin 16) (p : Fin 120) :
    (compiledSelectorRow T p).Valid T p := by
  fin_cases T
  · exact CompiledSelectorChecks.mask00_valid p
  · exact CompiledSelectorChecks.mask01_valid p
  · exact CompiledSelectorChecks.mask02_valid p
  · exact CompiledSelectorChecks.mask03_valid p
  · exact CompiledSelectorChecks.mask04_valid p
  · exact CompiledSelectorChecks.mask05_valid p
  · exact CompiledSelectorChecks.mask06_valid p
  · exact CompiledSelectorChecks.mask07_valid p
  · exact CompiledSelectorChecks.mask08_valid p
  · exact CompiledSelectorChecks.mask09_valid p
  · exact CompiledSelectorChecks.mask10_valid p
  · exact CompiledSelectorChecks.mask11_valid p
  · exact CompiledSelectorChecks.mask12_valid p
  · exact CompiledSelectorChecks.mask13_valid p
  · exact CompiledSelectorChecks.mask14_valid p
  · exact CompiledSelectorChecks.mask15_valid p


theorem compiledSelectorRow_chain (T : Fin 16) (p : Fin 120) (j : Fin 4) :
    (compiledSelectorRow T p).chain j=maskedChain T p j :=
  (compiledSelectorRow_valid T p).1 j

theorem compiledSelectorRow_coarse (T : Fin 16) (p : Fin 120) (j : Fin 10) :
    (compiledSelectorRow T p).coarse j=maskedCoarse T p j :=
  (compiledSelectorRow_valid T p).2.1 j

theorem compiledSelectorRow_coefficients (T : Fin 16) (p : Fin 120) (j i : Fin 4) :
    ((compiledSelectorRow T p).chainCoefficients j).toForm i=
      (maskedChain T p j).integerForm starIntegerSubsetForms i :=
  (compiledSelectorRow_valid T p).2.2 j i

#print axioms compiledSelectorRow_chain
#print axioms compiledSelectorRow_coarse
#print axioms compiledSelectorRow_coefficients
end MaxCaterpillar.Frontier.StarCertificate
