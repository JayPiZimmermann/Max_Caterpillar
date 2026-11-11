import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0112
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0113
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0114
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0115
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0116
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0117
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0118
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0119
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0112
def descriptor312 : OrbitDescriptor := ⟨27, 4, false⟩

theorem checked312 : orbitPatternTransform descriptor312 (Generated.Chunk0112.pattern312) =
    orbitRepresentativePattern descriptor312.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf312 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0112.pattern312 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0112.pattern312) descriptor312 checked312 (hRep descriptor312.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0112.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0112.regionContext := by
  apply Generated.FunctionalChunk0112.valid
  · exact leaf312 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0112

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0113
def descriptor313 : OrbitDescriptor := ⟨63, 0, false⟩

theorem checked313 : orbitPatternTransform descriptor313 (Generated.Chunk0113.pattern313) =
    orbitRepresentativePattern descriptor313.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf313 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0113.pattern313 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0113.pattern313) descriptor313 checked313 (hRep descriptor313.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0113.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0113.regionContext := by
  apply Generated.FunctionalChunk0113.valid
  · exact leaf313 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0113

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0114
def descriptor314 : OrbitDescriptor := ⟨64, 0, false⟩

theorem checked314 : orbitPatternTransform descriptor314 (Generated.Chunk0114.pattern314) =
    orbitRepresentativePattern descriptor314.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf314 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0114.pattern314 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0114.pattern314) descriptor314 checked314 (hRep descriptor314.representative)

def descriptor315 : OrbitDescriptor := ⟨65, 0, false⟩

theorem checked315 : orbitPatternTransform descriptor315 (Generated.Chunk0114.pattern315) =
    orbitRepresentativePattern descriptor315.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf315 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0114.pattern315 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0114.pattern315) descriptor315 checked315 (hRep descriptor315.representative)

def descriptor316 : OrbitDescriptor := ⟨64, 21, true⟩

theorem checked316 : orbitPatternTransform descriptor316 (Generated.Chunk0114.pattern316) =
    orbitRepresentativePattern descriptor316.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf316 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0114.pattern316 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0114.pattern316) descriptor316 checked316 (hRep descriptor316.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0114.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0114.regionContext := by
  apply Generated.FunctionalChunk0114.valid
  · exact leaf314 hRep
  · exact leaf315 hRep
  · exact leaf316 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0114

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0115
def descriptor317 : OrbitDescriptor := ⟨28, 4, false⟩

theorem checked317 : orbitPatternTransform descriptor317 (Generated.Chunk0115.pattern317) =
    orbitRepresentativePattern descriptor317.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf317 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0115.pattern317 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0115.pattern317) descriptor317 checked317 (hRep descriptor317.representative)

def descriptor318 : OrbitDescriptor := ⟨29, 4, false⟩

theorem checked318 : orbitPatternTransform descriptor318 (Generated.Chunk0115.pattern318) =
    orbitRepresentativePattern descriptor318.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf318 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0115.pattern318 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0115.pattern318) descriptor318 checked318 (hRep descriptor318.representative)

def descriptor319 : OrbitDescriptor := ⟨30, 4, false⟩

theorem checked319 : orbitPatternTransform descriptor319 (Generated.Chunk0115.pattern319) =
    orbitRepresentativePattern descriptor319.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf319 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0115.pattern319 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0115.pattern319) descriptor319 checked319 (hRep descriptor319.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0115.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0115.regionContext := by
  apply Generated.FunctionalChunk0115.valid
  · exact leaf317 hRep
  · exact leaf318 hRep
  · exact leaf319 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0115

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0116
def descriptor320 : OrbitDescriptor := ⟨64, 1, false⟩

theorem checked320 : orbitPatternTransform descriptor320 (Generated.Chunk0116.pattern320) =
    orbitRepresentativePattern descriptor320.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf320 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0116.pattern320 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0116.pattern320) descriptor320 checked320 (hRep descriptor320.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0116.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0116.regionContext := by
  apply Generated.FunctionalChunk0116.valid
  · exact leaf320 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0116

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0117
def descriptor321 : OrbitDescriptor := ⟨35, 17, true⟩

theorem checked321 : orbitPatternTransform descriptor321 (Generated.Chunk0117.pattern321) =
    orbitRepresentativePattern descriptor321.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf321 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0117.pattern321 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0117.pattern321) descriptor321 checked321 (hRep descriptor321.representative)

def descriptor322 : OrbitDescriptor := ⟨34, 17, true⟩

theorem checked322 : orbitPatternTransform descriptor322 (Generated.Chunk0117.pattern322) =
    orbitRepresentativePattern descriptor322.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf322 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0117.pattern322 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0117.pattern322) descriptor322 checked322 (hRep descriptor322.representative)

def descriptor323 : OrbitDescriptor := ⟨33, 17, true⟩

theorem checked323 : orbitPatternTransform descriptor323 (Generated.Chunk0117.pattern323) =
    orbitRepresentativePattern descriptor323.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf323 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0117.pattern323 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0117.pattern323) descriptor323 checked323 (hRep descriptor323.representative)

def descriptor324 : OrbitDescriptor := ⟨32, 23, true⟩

theorem checked324 : orbitPatternTransform descriptor324 (Generated.Chunk0117.pattern324) =
    orbitRepresentativePattern descriptor324.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf324 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0117.pattern324 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0117.pattern324) descriptor324 checked324 (hRep descriptor324.representative)

def descriptor325 : OrbitDescriptor := ⟨30, 23, true⟩

theorem checked325 : orbitPatternTransform descriptor325 (Generated.Chunk0117.pattern325) =
    orbitRepresentativePattern descriptor325.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf325 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0117.pattern325 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0117.pattern325) descriptor325 checked325 (hRep descriptor325.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0117.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0117.regionContext := by
  apply Generated.FunctionalChunk0117.valid
  · exact leaf321 hRep
  · exact leaf322 hRep
  · exact leaf323 hRep
  · exact leaf324 hRep
  · exact leaf325 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0117

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0118
def descriptor326 : OrbitDescriptor := ⟨29, 18, false⟩

theorem checked326 : orbitPatternTransform descriptor326 (Generated.Chunk0118.pattern326) =
    orbitRepresentativePattern descriptor326.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf326 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0118.pattern326 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0118.pattern326) descriptor326 checked326 (hRep descriptor326.representative)

def descriptor327 : OrbitDescriptor := ⟨31, 4, false⟩

theorem checked327 : orbitPatternTransform descriptor327 (Generated.Chunk0118.pattern327) =
    orbitRepresentativePattern descriptor327.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf327 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0118.pattern327 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0118.pattern327) descriptor327 checked327 (hRep descriptor327.representative)

def descriptor328 : OrbitDescriptor := ⟨32, 4, false⟩

theorem checked328 : orbitPatternTransform descriptor328 (Generated.Chunk0118.pattern328) =
    orbitRepresentativePattern descriptor328.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf328 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0118.pattern328 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0118.pattern328) descriptor328 checked328 (hRep descriptor328.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0118.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0118.regionContext := by
  apply Generated.FunctionalChunk0118.valid
  · exact leaf326 hRep
  · exact leaf327 hRep
  · exact leaf328 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0118

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0119
def descriptor329 : OrbitDescriptor := ⟨65, 1, false⟩

theorem checked329 : orbitPatternTransform descriptor329 (Generated.Chunk0119.pattern329) =
    orbitRepresentativePattern descriptor329.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf329 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0119.pattern329 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0119.pattern329) descriptor329 checked329 (hRep descriptor329.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0119.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0119.regionContext := by
  apply Generated.FunctionalChunk0119.valid
  · exact leaf329 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0119
