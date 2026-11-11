import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0040
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0041
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0042
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0043
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0044
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0045
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0046
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0047
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0040
def descriptor110 : OrbitDescriptor := ⟨50, 0, false⟩

theorem checked110 : orbitPatternTransform descriptor110 (Generated.Chunk0040.pattern110) =
    orbitRepresentativePattern descriptor110.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf110 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0040.pattern110 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0040.pattern110) descriptor110 checked110 (hRep descriptor110.representative)

def descriptor111 : OrbitDescriptor := ⟨51, 0, false⟩

theorem checked111 : orbitPatternTransform descriptor111 (Generated.Chunk0040.pattern111) =
    orbitRepresentativePattern descriptor111.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf111 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0040.pattern111 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0040.pattern111) descriptor111 checked111 (hRep descriptor111.representative)

def descriptor112 : OrbitDescriptor := ⟨52, 0, false⟩

theorem checked112 : orbitPatternTransform descriptor112 (Generated.Chunk0040.pattern112) =
    orbitRepresentativePattern descriptor112.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf112 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0040.pattern112 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0040.pattern112) descriptor112 checked112 (hRep descriptor112.representative)

def descriptor113 : OrbitDescriptor := ⟨53, 0, false⟩

theorem checked113 : orbitPatternTransform descriptor113 (Generated.Chunk0040.pattern113) =
    orbitRepresentativePattern descriptor113.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf113 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0040.pattern113 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0040.pattern113) descriptor113 checked113 (hRep descriptor113.representative)

def descriptor114 : OrbitDescriptor := ⟨54, 0, false⟩

theorem checked114 : orbitPatternTransform descriptor114 (Generated.Chunk0040.pattern114) =
    orbitRepresentativePattern descriptor114.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf114 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0040.pattern114 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0040.pattern114) descriptor114 checked114 (hRep descriptor114.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0040.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0040.regionContext := by
  apply Generated.FunctionalChunk0040.valid
  · exact leaf110 hRep
  · exact leaf111 hRep
  · exact leaf112 hRep
  · exact leaf113 hRep
  · exact leaf114 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0040

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0041
def descriptor115 : OrbitDescriptor := ⟨3, 4, false⟩

theorem checked115 : orbitPatternTransform descriptor115 (Generated.Chunk0041.pattern115) =
    orbitRepresentativePattern descriptor115.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf115 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0041.pattern115 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0041.pattern115) descriptor115 checked115 (hRep descriptor115.representative)

def descriptor116 : OrbitDescriptor := ⟨5, 1, false⟩

theorem checked116 : orbitPatternTransform descriptor116 (Generated.Chunk0041.pattern116) =
    orbitRepresentativePattern descriptor116.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf116 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0041.pattern116 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0041.pattern116) descriptor116 checked116 (hRep descriptor116.representative)

def descriptor117 : OrbitDescriptor := ⟨6, 1, false⟩

theorem checked117 : orbitPatternTransform descriptor117 (Generated.Chunk0041.pattern117) =
    orbitRepresentativePattern descriptor117.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf117 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0041.pattern117 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0041.pattern117) descriptor117 checked117 (hRep descriptor117.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0041.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0041.regionContext := by
  apply Generated.FunctionalChunk0041.valid
  · exact leaf115 hRep
  · exact leaf116 hRep
  · exact leaf117 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0041

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0042
def descriptor118 : OrbitDescriptor := ⟨29, 1, false⟩

theorem checked118 : orbitPatternTransform descriptor118 (Generated.Chunk0042.pattern118) =
    orbitRepresentativePattern descriptor118.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf118 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0042.pattern118 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0042.pattern118) descriptor118 checked118 (hRep descriptor118.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0042.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0042.regionContext := by
  apply Generated.FunctionalChunk0042.valid
  · exact leaf118 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0042

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0043
def descriptor119 : OrbitDescriptor := ⟨42, 1, false⟩

theorem checked119 : orbitPatternTransform descriptor119 (Generated.Chunk0043.pattern119) =
    orbitRepresentativePattern descriptor119.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf119 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0043.pattern119 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0043.pattern119) descriptor119 checked119 (hRep descriptor119.representative)

def descriptor120 : OrbitDescriptor := ⟨43, 1, false⟩

theorem checked120 : orbitPatternTransform descriptor120 (Generated.Chunk0043.pattern120) =
    orbitRepresentativePattern descriptor120.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf120 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0043.pattern120 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0043.pattern120) descriptor120 checked120 (hRep descriptor120.representative)

def descriptor121 : OrbitDescriptor := ⟨44, 1, false⟩

theorem checked121 : orbitPatternTransform descriptor121 (Generated.Chunk0043.pattern121) =
    orbitRepresentativePattern descriptor121.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf121 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0043.pattern121 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0043.pattern121) descriptor121 checked121 (hRep descriptor121.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0043.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0043.regionContext := by
  apply Generated.FunctionalChunk0043.valid
  · exact leaf119 hRep
  · exact leaf120 hRep
  · exact leaf121 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0043

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0044
def descriptor122 : OrbitDescriptor := ⟨55, 0, false⟩

theorem checked122 : orbitPatternTransform descriptor122 (Generated.Chunk0044.pattern122) =
    orbitRepresentativePattern descriptor122.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf122 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0044.pattern122 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0044.pattern122) descriptor122 checked122 (hRep descriptor122.representative)

def descriptor123 : OrbitDescriptor := ⟨56, 0, false⟩

theorem checked123 : orbitPatternTransform descriptor123 (Generated.Chunk0044.pattern123) =
    orbitRepresentativePattern descriptor123.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf123 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0044.pattern123 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0044.pattern123) descriptor123 checked123 (hRep descriptor123.representative)

def descriptor124 : OrbitDescriptor := ⟨57, 0, false⟩

theorem checked124 : orbitPatternTransform descriptor124 (Generated.Chunk0044.pattern124) =
    orbitRepresentativePattern descriptor124.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf124 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0044.pattern124 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0044.pattern124) descriptor124 checked124 (hRep descriptor124.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0044.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0044.regionContext := by
  apply Generated.FunctionalChunk0044.valid
  · exact leaf122 hRep
  · exact leaf123 hRep
  · exact leaf124 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0044

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0045
def descriptor125 : OrbitDescriptor := ⟨58, 0, false⟩

theorem checked125 : orbitPatternTransform descriptor125 (Generated.Chunk0045.pattern125) =
    orbitRepresentativePattern descriptor125.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf125 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0045.pattern125 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0045.pattern125) descriptor125 checked125 (hRep descriptor125.representative)

def descriptor126 : OrbitDescriptor := ⟨59, 0, false⟩

theorem checked126 : orbitPatternTransform descriptor126 (Generated.Chunk0045.pattern126) =
    orbitRepresentativePattern descriptor126.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf126 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0045.pattern126 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0045.pattern126) descriptor126 checked126 (hRep descriptor126.representative)

def descriptor127 : OrbitDescriptor := ⟨60, 0, false⟩

theorem checked127 : orbitPatternTransform descriptor127 (Generated.Chunk0045.pattern127) =
    orbitRepresentativePattern descriptor127.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf127 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0045.pattern127 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0045.pattern127) descriptor127 checked127 (hRep descriptor127.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0045.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0045.regionContext := by
  apply Generated.FunctionalChunk0045.valid
  · exact leaf125 hRep
  · exact leaf126 hRep
  · exact leaf127 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0045

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0046
def descriptor128 : OrbitDescriptor := ⟨61, 0, false⟩

theorem checked128 : orbitPatternTransform descriptor128 (Generated.Chunk0046.pattern128) =
    orbitRepresentativePattern descriptor128.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf128 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0046.pattern128 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0046.pattern128) descriptor128 checked128 (hRep descriptor128.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0046.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0046.regionContext := by
  apply Generated.FunctionalChunk0046.valid
  · exact leaf128 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0046

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0047
def descriptor129 : OrbitDescriptor := ⟨60, 23, true⟩

theorem checked129 : orbitPatternTransform descriptor129 (Generated.Chunk0047.pattern129) =
    orbitRepresentativePattern descriptor129.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf129 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0047.pattern129 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0047.pattern129) descriptor129 checked129 (hRep descriptor129.representative)

def descriptor130 : OrbitDescriptor := ⟨59, 23, true⟩

theorem checked130 : orbitPatternTransform descriptor130 (Generated.Chunk0047.pattern130) =
    orbitRepresentativePattern descriptor130.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf130 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0047.pattern130 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0047.pattern130) descriptor130 checked130 (hRep descriptor130.representative)

def descriptor131 : OrbitDescriptor := ⟨58, 23, true⟩

theorem checked131 : orbitPatternTransform descriptor131 (Generated.Chunk0047.pattern131) =
    orbitRepresentativePattern descriptor131.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf131 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0047.pattern131 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0047.pattern131) descriptor131 checked131 (hRep descriptor131.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0047.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0047.regionContext := by
  apply Generated.FunctionalChunk0047.valid
  · exact leaf129 hRep
  · exact leaf130 hRep
  · exact leaf131 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0047
