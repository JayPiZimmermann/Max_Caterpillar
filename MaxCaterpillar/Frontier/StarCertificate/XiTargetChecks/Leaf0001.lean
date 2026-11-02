import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.Chunk0001
import MaxCaterpillar.Frontier.StarCertificate.XiProfiles
import MaxCaterpillar.Frontier.StarCertificate.XiSparseCollect
import MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeSound
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0000
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0001
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0004
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0007
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0020
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0023
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0036
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0049
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0149
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0152
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0165
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0178
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0277
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0290
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0389
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0488

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf0001
open BigOperators

def pattern : Fin 15 → Sign := MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0001.pattern1
def psi (T : Fin 16) : Fin 16 → IntegerForm 4 :=
  if T.val < 8 then (
    if T.val < 4 then (
      if T.val < 2 then (
        if T.val < 1 then (
          XiProfileChecks.Profile0000.psi
        ) else (
          XiProfileChecks.Profile0001.psi
        )
      ) else (
        if T.val < 3 then (
          XiProfileChecks.Profile0004.psi
        ) else (
          XiProfileChecks.Profile0007.psi
        )
      )
    ) else (
      if T.val < 6 then (
        if T.val < 5 then (
          XiProfileChecks.Profile0020.psi
        ) else (
          XiProfileChecks.Profile0023.psi
        )
      ) else (
        if T.val < 7 then (
          XiProfileChecks.Profile0036.psi
        ) else (
          XiProfileChecks.Profile0049.psi
        )
      )
    )
  ) else (
    if T.val < 12 then (
      if T.val < 10 then (
        if T.val < 9 then (
          XiProfileChecks.Profile0149.psi
        ) else (
          XiProfileChecks.Profile0152.psi
        )
      ) else (
        if T.val < 11 then (
          XiProfileChecks.Profile0165.psi
        ) else (
          XiProfileChecks.Profile0178.psi
        )
      )
    ) else (
      if T.val < 14 then (
        if T.val < 13 then (
          XiProfileChecks.Profile0277.psi
        ) else (
          XiProfileChecks.Profile0290.psi
        )
      ) else (
        if T.val < 15 then (
          XiProfileChecks.Profile0389.psi
        ) else (
          XiProfileChecks.Profile0488.psi
        )
      )
    )
  )
def coefficients : Fin 80 → IntegerForm 4 := MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0001.coeff1

theorem restriction_0 : restrictPattern 0 pattern = XiProfileChecks.Profile0000.pattern := by decide
theorem restriction_1 : restrictPattern 1 pattern = XiProfileChecks.Profile0001.pattern := by decide
theorem restriction_2 : restrictPattern 2 pattern = XiProfileChecks.Profile0004.pattern := by decide
theorem restriction_3 : restrictPattern 3 pattern = XiProfileChecks.Profile0007.pattern := by decide
theorem restriction_4 : restrictPattern 4 pattern = XiProfileChecks.Profile0020.pattern := by decide
theorem restriction_5 : restrictPattern 5 pattern = XiProfileChecks.Profile0023.pattern := by decide
theorem restriction_6 : restrictPattern 6 pattern = XiProfileChecks.Profile0036.pattern := by decide
theorem restriction_7 : restrictPattern 7 pattern = XiProfileChecks.Profile0049.pattern := by decide
theorem restriction_8 : restrictPattern 8 pattern = XiProfileChecks.Profile0149.pattern := by decide
theorem restriction_9 : restrictPattern 9 pattern = XiProfileChecks.Profile0152.pattern := by decide
theorem restriction_10 : restrictPattern 10 pattern = XiProfileChecks.Profile0165.pattern := by decide
theorem restriction_11 : restrictPattern 11 pattern = XiProfileChecks.Profile0178.pattern := by decide
theorem restriction_12 : restrictPattern 12 pattern = XiProfileChecks.Profile0277.pattern := by decide
theorem restriction_13 : restrictPattern 13 pattern = XiProfileChecks.Profile0290.pattern := by decide
theorem restriction_14 : restrictPattern 14 pattern = XiProfileChecks.Profile0389.pattern := by decide
theorem restriction_15 : restrictPattern 15 pattern = XiProfileChecks.Profile0488.pattern := by decide

theorem psi_check (T P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients T P pattern i = psi T P i := by
  fin_cases T
  · change maskedPsiIntegerCoefficients 0 P pattern i = XiProfileChecks.Profile0000.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 0 P pattern) i, restriction_0]
    exact XiProfileChecks.Profile0000.actual_profile P i
  · change maskedPsiIntegerCoefficients 1 P pattern i = XiProfileChecks.Profile0001.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 1 P pattern) i, restriction_1]
    exact XiProfileChecks.Profile0001.actual_profile P i
  · change maskedPsiIntegerCoefficients 2 P pattern i = XiProfileChecks.Profile0004.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 2 P pattern) i, restriction_2]
    exact XiProfileChecks.Profile0004.actual_profile P i
  · change maskedPsiIntegerCoefficients 3 P pattern i = XiProfileChecks.Profile0007.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 3 P pattern) i, restriction_3]
    exact XiProfileChecks.Profile0007.actual_profile P i
  · change maskedPsiIntegerCoefficients 4 P pattern i = XiProfileChecks.Profile0020.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 4 P pattern) i, restriction_4]
    exact XiProfileChecks.Profile0020.actual_profile P i
  · change maskedPsiIntegerCoefficients 5 P pattern i = XiProfileChecks.Profile0023.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 5 P pattern) i, restriction_5]
    exact XiProfileChecks.Profile0023.actual_profile P i
  · change maskedPsiIntegerCoefficients 6 P pattern i = XiProfileChecks.Profile0036.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 6 P pattern) i, restriction_6]
    exact XiProfileChecks.Profile0036.actual_profile P i
  · change maskedPsiIntegerCoefficients 7 P pattern i = XiProfileChecks.Profile0049.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 7 P pattern) i, restriction_7]
    exact XiProfileChecks.Profile0049.actual_profile P i
  · change maskedPsiIntegerCoefficients 8 P pattern i = XiProfileChecks.Profile0149.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 8 P pattern) i, restriction_8]
    exact XiProfileChecks.Profile0149.actual_profile P i
  · change maskedPsiIntegerCoefficients 9 P pattern i = XiProfileChecks.Profile0152.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 9 P pattern) i, restriction_9]
    exact XiProfileChecks.Profile0152.actual_profile P i
  · change maskedPsiIntegerCoefficients 10 P pattern i = XiProfileChecks.Profile0165.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 10 P pattern) i, restriction_10]
    exact XiProfileChecks.Profile0165.actual_profile P i
  · change maskedPsiIntegerCoefficients 11 P pattern i = XiProfileChecks.Profile0178.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 11 P pattern) i, restriction_11]
    exact XiProfileChecks.Profile0178.actual_profile P i
  · change maskedPsiIntegerCoefficients 12 P pattern i = XiProfileChecks.Profile0277.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 12 P pattern) i, restriction_12]
    exact XiProfileChecks.Profile0277.actual_profile P i
  · change maskedPsiIntegerCoefficients 13 P pattern i = XiProfileChecks.Profile0290.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 13 P pattern) i, restriction_13]
    exact XiProfileChecks.Profile0290.actual_profile P i
  · change maskedPsiIntegerCoefficients 14 P pattern i = XiProfileChecks.Profile0389.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 14 P pattern) i, restriction_14]
    exact XiProfileChecks.Profile0389.actual_profile P i
  · change maskedPsiIntegerCoefficients 15 P pattern i = XiProfileChecks.Profile0488.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict 15 P pattern) i, restriction_15]
    exact XiProfileChecks.Profile0488.actual_profile P i

theorem collect_fast_check : integerTable2Check (sparseCollect psi) coefficients = true := by
  kernel_bool_check

theorem actual_match : starAnovaIntegerCoefficients pattern = coefficients := by
  rw [starAnovaIntegerCoefficients_of_sparse_table pattern psi psi_check]
  funext t i
  exact integerTable2Check_sound _ _ collect_fast_check t i

theorem stratum_sound (z : Fin 4 → ℝ) (hz : actualSigns subsetForms z = pattern) : AllStarAnovaZero z :=
  starAnova_stratum_sound pattern coefficients MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0001.den1 MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0001.lambda1
    MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0001.solvedNumeric1.2 actual_match z hz

end MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf0001
