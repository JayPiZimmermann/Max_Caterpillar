import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0120
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0121
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0122
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0123
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0124
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0125
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0126
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0127
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0120
def descriptor330 : OrbitDescriptor := ⟨32, 17, true⟩

theorem checked330 : orbitPatternTransform descriptor330 (Generated.Chunk0120.pattern330) =
    orbitRepresentativePattern descriptor330.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf330 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0120.pattern330 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0120.pattern330) descriptor330 checked330 (hRep descriptor330.representative)

def descriptor331 : OrbitDescriptor := ⟨31, 17, true⟩

theorem checked331 : orbitPatternTransform descriptor331 (Generated.Chunk0120.pattern331) =
    orbitRepresentativePattern descriptor331.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf331 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0120.pattern331 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0120.pattern331) descriptor331 checked331 (hRep descriptor331.representative)

def descriptor332 : OrbitDescriptor := ⟨29, 23, true⟩

theorem checked332 : orbitPatternTransform descriptor332 (Generated.Chunk0120.pattern332) =
    orbitRepresentativePattern descriptor332.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf332 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0120.pattern332 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0120.pattern332) descriptor332 checked332 (hRep descriptor332.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0120.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0120.regionContext := by
  apply Generated.FunctionalChunk0120.valid
  · exact leaf330 hRep
  · exact leaf331 hRep
  · exact leaf332 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0120

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0121
def descriptor333 : OrbitDescriptor := ⟨30, 18, false⟩

theorem checked333 : orbitPatternTransform descriptor333 (Generated.Chunk0121.pattern333) =
    orbitRepresentativePattern descriptor333.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf333 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0121.pattern333 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0121.pattern333) descriptor333 checked333 (hRep descriptor333.representative)

def descriptor334 : OrbitDescriptor := ⟨32, 18, false⟩

theorem checked334 : orbitPatternTransform descriptor334 (Generated.Chunk0121.pattern334) =
    orbitRepresentativePattern descriptor334.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf334 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0121.pattern334 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0121.pattern334) descriptor334 checked334 (hRep descriptor334.representative)

def descriptor335 : OrbitDescriptor := ⟨33, 4, false⟩

theorem checked335 : orbitPatternTransform descriptor335 (Generated.Chunk0121.pattern335) =
    orbitRepresentativePattern descriptor335.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf335 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0121.pattern335 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0121.pattern335) descriptor335 checked335 (hRep descriptor335.representative)

def descriptor336 : OrbitDescriptor := ⟨34, 4, false⟩

theorem checked336 : orbitPatternTransform descriptor336 (Generated.Chunk0121.pattern336) =
    orbitRepresentativePattern descriptor336.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf336 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0121.pattern336 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0121.pattern336) descriptor336 checked336 (hRep descriptor336.representative)

def descriptor337 : OrbitDescriptor := ⟨35, 4, false⟩

theorem checked337 : orbitPatternTransform descriptor337 (Generated.Chunk0121.pattern337) =
    orbitRepresentativePattern descriptor337.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf337 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0121.pattern337 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0121.pattern337) descriptor337 checked337 (hRep descriptor337.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0121.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0121.regionContext := by
  apply Generated.FunctionalChunk0121.valid
  · exact leaf333 hRep
  · exact leaf334 hRep
  · exact leaf335 hRep
  · exact leaf336 hRep
  · exact leaf337 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0121

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0122
def descriptor338 : OrbitDescriptor := ⟨64, 15, true⟩

theorem checked338 : orbitPatternTransform descriptor338 (Generated.Chunk0122.pattern338) =
    orbitRepresentativePattern descriptor338.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf338 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0122.pattern338 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0122.pattern338) descriptor338 checked338 (hRep descriptor338.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0122.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0122.regionContext := by
  apply Generated.FunctionalChunk0122.valid
  · exact leaf338 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0122

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0123
def descriptor339 : OrbitDescriptor := ⟨30, 17, true⟩

theorem checked339 : orbitPatternTransform descriptor339 (Generated.Chunk0123.pattern339) =
    orbitRepresentativePattern descriptor339.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf339 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0123.pattern339 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0123.pattern339) descriptor339 checked339 (hRep descriptor339.representative)

def descriptor340 : OrbitDescriptor := ⟨29, 17, true⟩

theorem checked340 : orbitPatternTransform descriptor340 (Generated.Chunk0123.pattern340) =
    orbitRepresentativePattern descriptor340.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf340 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0123.pattern340 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0123.pattern340) descriptor340 checked340 (hRep descriptor340.representative)

def descriptor341 : OrbitDescriptor := ⟨28, 17, true⟩

theorem checked341 : orbitPatternTransform descriptor341 (Generated.Chunk0123.pattern341) =
    orbitRepresentativePattern descriptor341.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf341 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0123.pattern341 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0123.pattern341) descriptor341 checked341 (hRep descriptor341.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0123.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0123.regionContext := by
  apply Generated.FunctionalChunk0123.valid
  · exact leaf339 hRep
  · exact leaf340 hRep
  · exact leaf341 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0123

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0124
def descriptor342 : OrbitDescriptor := ⟨2, 3, false⟩

theorem checked342 : orbitPatternTransform descriptor342 (Generated.Chunk0124.pattern342) =
    orbitRepresentativePattern descriptor342.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf342 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0124.pattern342 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0124.pattern342) descriptor342 checked342 (hRep descriptor342.representative)

def descriptor343 : OrbitDescriptor := ⟨3, 3, false⟩

theorem checked343 : orbitPatternTransform descriptor343 (Generated.Chunk0124.pattern343) =
    orbitRepresentativePattern descriptor343.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf343 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0124.pattern343 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0124.pattern343) descriptor343 checked343 (hRep descriptor343.representative)

def descriptor344 : OrbitDescriptor := ⟨4, 3, false⟩

theorem checked344 : orbitPatternTransform descriptor344 (Generated.Chunk0124.pattern344) =
    orbitRepresentativePattern descriptor344.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf344 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0124.pattern344 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0124.pattern344) descriptor344 checked344 (hRep descriptor344.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0124.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0124.regionContext := by
  apply Generated.FunctionalChunk0124.valid
  · exact leaf342 hRep
  · exact leaf343 hRep
  · exact leaf344 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0124

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0125
def descriptor345 : OrbitDescriptor := ⟨28, 3, false⟩

theorem checked345 : orbitPatternTransform descriptor345 (Generated.Chunk0125.pattern345) =
    orbitRepresentativePattern descriptor345.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf345 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0125.pattern345 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0125.pattern345) descriptor345 checked345 (hRep descriptor345.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0125.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0125.regionContext := by
  apply Generated.FunctionalChunk0125.valid
  · exact leaf345 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0125

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0126
def descriptor346 : OrbitDescriptor := ⟨36, 2, false⟩

theorem checked346 : orbitPatternTransform descriptor346 (Generated.Chunk0126.pattern346) =
    orbitRepresentativePattern descriptor346.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf346 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0126.pattern346 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0126.pattern346) descriptor346 checked346 (hRep descriptor346.representative)

def descriptor347 : OrbitDescriptor := ⟨37, 2, false⟩

theorem checked347 : orbitPatternTransform descriptor347 (Generated.Chunk0126.pattern347) =
    orbitRepresentativePattern descriptor347.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf347 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0126.pattern347 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0126.pattern347) descriptor347 checked347 (hRep descriptor347.representative)

def descriptor348 : OrbitDescriptor := ⟨38, 2, false⟩

theorem checked348 : orbitPatternTransform descriptor348 (Generated.Chunk0126.pattern348) =
    orbitRepresentativePattern descriptor348.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf348 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0126.pattern348 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0126.pattern348) descriptor348 checked348 (hRep descriptor348.representative)

def descriptor349 : OrbitDescriptor := ⟨42, 2, false⟩

theorem checked349 : orbitPatternTransform descriptor349 (Generated.Chunk0126.pattern349) =
    orbitRepresentativePattern descriptor349.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf349 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0126.pattern349 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0126.pattern349) descriptor349 checked349 (hRep descriptor349.representative)

def descriptor350 : OrbitDescriptor := ⟨45, 2, false⟩

theorem checked350 : orbitPatternTransform descriptor350 (Generated.Chunk0126.pattern350) =
    orbitRepresentativePattern descriptor350.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf350 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0126.pattern350 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0126.pattern350) descriptor350 checked350 (hRep descriptor350.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0126.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0126.regionContext := by
  apply Generated.FunctionalChunk0126.valid
  · exact leaf346 hRep
  · exact leaf347 hRep
  · exact leaf348 hRep
  · exact leaf349 hRep
  · exact leaf350 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0126

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0127
def descriptor351 : OrbitDescriptor := ⟨37, 12, false⟩

theorem checked351 : orbitPatternTransform descriptor351 (Generated.Chunk0127.pattern351) =
    orbitRepresentativePattern descriptor351.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf351 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0127.pattern351 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0127.pattern351) descriptor351 checked351 (hRep descriptor351.representative)

def descriptor352 : OrbitDescriptor := ⟨39, 2, false⟩

theorem checked352 : orbitPatternTransform descriptor352 (Generated.Chunk0127.pattern352) =
    orbitRepresentativePattern descriptor352.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf352 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0127.pattern352 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0127.pattern352) descriptor352 checked352 (hRep descriptor352.representative)

def descriptor353 : OrbitDescriptor := ⟨40, 2, false⟩

theorem checked353 : orbitPatternTransform descriptor353 (Generated.Chunk0127.pattern353) =
    orbitRepresentativePattern descriptor353.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf353 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0127.pattern353 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0127.pattern353) descriptor353 checked353 (hRep descriptor353.representative)

def descriptor354 : OrbitDescriptor := ⟨43, 2, false⟩

theorem checked354 : orbitPatternTransform descriptor354 (Generated.Chunk0127.pattern354) =
    orbitRepresentativePattern descriptor354.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf354 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0127.pattern354 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0127.pattern354) descriptor354 checked354 (hRep descriptor354.representative)

def descriptor355 : OrbitDescriptor := ⟨46, 2, false⟩

theorem checked355 : orbitPatternTransform descriptor355 (Generated.Chunk0127.pattern355) =
    orbitRepresentativePattern descriptor355.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf355 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0127.pattern355 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0127.pattern355) descriptor355 checked355 (hRep descriptor355.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0127.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0127.regionContext := by
  apply Generated.FunctionalChunk0127.valid
  · exact leaf351 hRep
  · exact leaf352 hRep
  · exact leaf353 hRep
  · exact leaf354 hRep
  · exact leaf355 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0127
