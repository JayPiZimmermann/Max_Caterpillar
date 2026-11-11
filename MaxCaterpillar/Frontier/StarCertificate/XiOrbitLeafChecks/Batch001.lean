import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0008
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0009
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0010
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0011
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0012
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0013
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0014
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0015
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0008
def descriptor24 : OrbitDescriptor := ⟨4, 8, false⟩

theorem checked24 : orbitPatternTransform descriptor24 (Generated.Chunk0008.pattern24) =
    orbitRepresentativePattern descriptor24.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf24 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0008.pattern24 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0008.pattern24) descriptor24 checked24 (hRep descriptor24.representative)

def descriptor25 : OrbitDescriptor := ⟨6, 8, false⟩

theorem checked25 : orbitPatternTransform descriptor25 (Generated.Chunk0008.pattern25) =
    orbitRepresentativePattern descriptor25.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf25 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0008.pattern25 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0008.pattern25) descriptor25 checked25 (hRep descriptor25.representative)

def descriptor26 : OrbitDescriptor := ⟨7, 6, false⟩

theorem checked26 : orbitPatternTransform descriptor26 (Generated.Chunk0008.pattern26) =
    orbitRepresentativePattern descriptor26.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf26 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0008.pattern26 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0008.pattern26) descriptor26 checked26 (hRep descriptor26.representative)

def descriptor27 : OrbitDescriptor := ⟨8, 6, false⟩

theorem checked27 : orbitPatternTransform descriptor27 (Generated.Chunk0008.pattern27) =
    orbitRepresentativePattern descriptor27.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf27 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0008.pattern27 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0008.pattern27) descriptor27 checked27 (hRep descriptor27.representative)

def descriptor28 : OrbitDescriptor := ⟨9, 6, false⟩

theorem checked28 : orbitPatternTransform descriptor28 (Generated.Chunk0008.pattern28) =
    orbitRepresentativePattern descriptor28.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf28 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0008.pattern28 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0008.pattern28) descriptor28 checked28 (hRep descriptor28.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0008.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0008.regionContext := by
  apply Generated.FunctionalChunk0008.valid
  · exact leaf24 hRep
  · exact leaf25 hRep
  · exact leaf26 hRep
  · exact leaf27 hRep
  · exact leaf28 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0008

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0009
def descriptor29 : OrbitDescriptor := ⟨6, 14, false⟩

theorem checked29 : orbitPatternTransform descriptor29 (Generated.Chunk0009.pattern29) =
    orbitRepresentativePattern descriptor29.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf29 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0009.pattern29 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0009.pattern29) descriptor29 checked29 (hRep descriptor29.representative)

def descriptor30 : OrbitDescriptor := ⟨11, 8, false⟩

theorem checked30 : orbitPatternTransform descriptor30 (Generated.Chunk0009.pattern30) =
    orbitRepresentativePattern descriptor30.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf30 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0009.pattern30 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0009.pattern30) descriptor30 checked30 (hRep descriptor30.representative)

def descriptor31 : OrbitDescriptor := ⟨12, 6, false⟩

theorem checked31 : orbitPatternTransform descriptor31 (Generated.Chunk0009.pattern31) =
    orbitRepresentativePattern descriptor31.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf31 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0009.pattern31 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0009.pattern31) descriptor31 checked31 (hRep descriptor31.representative)

def descriptor32 : OrbitDescriptor := ⟨13, 6, false⟩

theorem checked32 : orbitPatternTransform descriptor32 (Generated.Chunk0009.pattern32) =
    orbitRepresentativePattern descriptor32.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf32 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0009.pattern32 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0009.pattern32) descriptor32 checked32 (hRep descriptor32.representative)

def descriptor33 : OrbitDescriptor := ⟨14, 6, false⟩

theorem checked33 : orbitPatternTransform descriptor33 (Generated.Chunk0009.pattern33) =
    orbitRepresentativePattern descriptor33.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf33 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0009.pattern33 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0009.pattern33) descriptor33 checked33 (hRep descriptor33.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0009.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0009.regionContext := by
  apply Generated.FunctionalChunk0009.valid
  · exact leaf29 hRep
  · exact leaf30 hRep
  · exact leaf31 hRep
  · exact leaf32 hRep
  · exact leaf33 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0009

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0010
def descriptor34 : OrbitDescriptor := ⟨7, 12, false⟩

theorem checked34 : orbitPatternTransform descriptor34 (Generated.Chunk0010.pattern34) =
    orbitRepresentativePattern descriptor34.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf34 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0010.pattern34 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0010.pattern34) descriptor34 checked34 (hRep descriptor34.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0010.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0010.regionContext := by
  apply Generated.FunctionalChunk0010.valid
  · exact leaf34 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0010

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0011
def descriptor35 : OrbitDescriptor := ⟨12, 12, false⟩

theorem checked35 : orbitPatternTransform descriptor35 (Generated.Chunk0011.pattern35) =
    orbitRepresentativePattern descriptor35.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf35 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0011.pattern35 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0011.pattern35) descriptor35 checked35 (hRep descriptor35.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0011.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0011.regionContext := by
  apply Generated.FunctionalChunk0011.valid
  · exact leaf35 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0011

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0012
def descriptor36 : OrbitDescriptor := ⟨15, 0, false⟩

theorem checked36 : orbitPatternTransform descriptor36 (Generated.Chunk0012.pattern36) =
    orbitRepresentativePattern descriptor36.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf36 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0012.pattern36 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0012.pattern36) descriptor36 checked36 (hRep descriptor36.representative)

def descriptor37 : OrbitDescriptor := ⟨16, 0, false⟩

theorem checked37 : orbitPatternTransform descriptor37 (Generated.Chunk0012.pattern37) =
    orbitRepresentativePattern descriptor37.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf37 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0012.pattern37 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0012.pattern37) descriptor37 checked37 (hRep descriptor37.representative)

def descriptor38 : OrbitDescriptor := ⟨17, 0, false⟩

theorem checked38 : orbitPatternTransform descriptor38 (Generated.Chunk0012.pattern38) =
    orbitRepresentativePattern descriptor38.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf38 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0012.pattern38 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0012.pattern38) descriptor38 checked38 (hRep descriptor38.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0012.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0012.regionContext := by
  apply Generated.FunctionalChunk0012.valid
  · exact leaf36 hRep
  · exact leaf37 hRep
  · exact leaf38 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0012

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0013
def descriptor39 : OrbitDescriptor := ⟨16, 6, false⟩

theorem checked39 : orbitPatternTransform descriptor39 (Generated.Chunk0013.pattern39) =
    orbitRepresentativePattern descriptor39.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf39 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0013.pattern39 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0013.pattern39) descriptor39 checked39 (hRep descriptor39.representative)

def descriptor40 : OrbitDescriptor := ⟨18, 0, false⟩

theorem checked40 : orbitPatternTransform descriptor40 (Generated.Chunk0013.pattern40) =
    orbitRepresentativePattern descriptor40.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf40 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0013.pattern40 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0013.pattern40) descriptor40 checked40 (hRep descriptor40.representative)

def descriptor41 : OrbitDescriptor := ⟨19, 0, false⟩

theorem checked41 : orbitPatternTransform descriptor41 (Generated.Chunk0013.pattern41) =
    orbitRepresentativePattern descriptor41.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf41 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0013.pattern41 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0013.pattern41) descriptor41 checked41 (hRep descriptor41.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0013.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0013.regionContext := by
  apply Generated.FunctionalChunk0013.valid
  · exact leaf39 hRep
  · exact leaf40 hRep
  · exact leaf41 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0013

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0014
def descriptor42 : OrbitDescriptor := ⟨17, 6, false⟩

theorem checked42 : orbitPatternTransform descriptor42 (Generated.Chunk0014.pattern42) =
    orbitRepresentativePattern descriptor42.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf42 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0014.pattern42 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0014.pattern42) descriptor42 checked42 (hRep descriptor42.representative)

def descriptor43 : OrbitDescriptor := ⟨19, 6, false⟩

theorem checked43 : orbitPatternTransform descriptor43 (Generated.Chunk0014.pattern43) =
    orbitRepresentativePattern descriptor43.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf43 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0014.pattern43 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0014.pattern43) descriptor43 checked43 (hRep descriptor43.representative)

def descriptor44 : OrbitDescriptor := ⟨20, 0, false⟩

theorem checked44 : orbitPatternTransform descriptor44 (Generated.Chunk0014.pattern44) =
    orbitRepresentativePattern descriptor44.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf44 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0014.pattern44 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0014.pattern44) descriptor44 checked44 (hRep descriptor44.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0014.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0014.regionContext := by
  apply Generated.FunctionalChunk0014.valid
  · exact leaf42 hRep
  · exact leaf43 hRep
  · exact leaf44 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0014

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0015
def descriptor45 : OrbitDescriptor := ⟨8, 12, false⟩

theorem checked45 : orbitPatternTransform descriptor45 (Generated.Chunk0015.pattern45) =
    orbitRepresentativePattern descriptor45.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf45 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0015.pattern45 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0015.pattern45) descriptor45 checked45 (hRep descriptor45.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0015.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0015.regionContext := by
  apply Generated.FunctionalChunk0015.valid
  · exact leaf45 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0015
