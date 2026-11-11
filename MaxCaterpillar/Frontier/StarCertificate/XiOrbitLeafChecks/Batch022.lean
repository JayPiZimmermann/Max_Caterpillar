import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0176
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0177
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0178
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0179
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0180
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0181
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0182
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0183
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0176
def descriptor494 : OrbitDescriptor := ⟨7, 21, true⟩

theorem checked494 : orbitPatternTransform descriptor494 (Generated.Chunk0176.pattern494) =
    orbitRepresentativePattern descriptor494.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf494 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0176.pattern494 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0176.pattern494) descriptor494 checked494 (hRep descriptor494.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0176.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0176.regionContext := by
  apply Generated.FunctionalChunk0176.valid
  · exact leaf494 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0176

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0177
def descriptor495 : OrbitDescriptor := ⟨42, 18, false⟩

theorem checked495 : orbitPatternTransform descriptor495 (Generated.Chunk0177.pattern495) =
    orbitRepresentativePattern descriptor495.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf495 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern495 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern495) descriptor495 checked495 (hRep descriptor495.representative)

def descriptor496 : OrbitDescriptor := ⟨43, 18, false⟩

theorem checked496 : orbitPatternTransform descriptor496 (Generated.Chunk0177.pattern496) =
    orbitRepresentativePattern descriptor496.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf496 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern496 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern496) descriptor496 checked496 (hRep descriptor496.representative)

def descriptor497 : OrbitDescriptor := ⟨44, 18, false⟩

theorem checked497 : orbitPatternTransform descriptor497 (Generated.Chunk0177.pattern497) =
    orbitRepresentativePattern descriptor497.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf497 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern497 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern497) descriptor497 checked497 (hRep descriptor497.representative)

def descriptor498 : OrbitDescriptor := ⟨48, 4, false⟩

theorem checked498 : orbitPatternTransform descriptor498 (Generated.Chunk0177.pattern498) =
    orbitRepresentativePattern descriptor498.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf498 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern498 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern498) descriptor498 checked498 (hRep descriptor498.representative)

def descriptor499 : OrbitDescriptor := ⟨49, 4, false⟩

theorem checked499 : orbitPatternTransform descriptor499 (Generated.Chunk0177.pattern499) =
    orbitRepresentativePattern descriptor499.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf499 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern499 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern499) descriptor499 checked499 (hRep descriptor499.representative)

def descriptor500 : OrbitDescriptor := ⟨61, 4, false⟩

theorem checked500 : orbitPatternTransform descriptor500 (Generated.Chunk0177.pattern500) =
    orbitRepresentativePattern descriptor500.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf500 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern500 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern500) descriptor500 checked500 (hRep descriptor500.representative)

def descriptor501 : OrbitDescriptor := ⟨49, 15, true⟩

theorem checked501 : orbitPatternTransform descriptor501 (Generated.Chunk0177.pattern501) =
    orbitRepresentativePattern descriptor501.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf501 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0177.pattern501 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0177.pattern501) descriptor501 checked501 (hRep descriptor501.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0177.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0177.regionContext := by
  apply Generated.FunctionalChunk0177.valid
  · exact leaf495 hRep
  · exact leaf496 hRep
  · exact leaf497 hRep
  · exact leaf498 hRep
  · exact leaf499 hRep
  · exact leaf500 hRep
  · exact leaf501 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0177

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0178
def descriptor502 : OrbitDescriptor := ⟨32, 15, true⟩

theorem checked502 : orbitPatternTransform descriptor502 (Generated.Chunk0178.pattern502) =
    orbitRepresentativePattern descriptor502.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf502 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0178.pattern502 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0178.pattern502) descriptor502 checked502 (hRep descriptor502.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0178.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0178.regionContext := by
  apply Generated.FunctionalChunk0178.valid
  · exact leaf502 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0178

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0179
def descriptor503 : OrbitDescriptor := ⟨14, 15, true⟩

theorem checked503 : orbitPatternTransform descriptor503 (Generated.Chunk0179.pattern503) =
    orbitRepresentativePattern descriptor503.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf503 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0179.pattern503 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0179.pattern503) descriptor503 checked503 (hRep descriptor503.representative)

def descriptor504 : OrbitDescriptor := ⟨13, 15, true⟩

theorem checked504 : orbitPatternTransform descriptor504 (Generated.Chunk0179.pattern504) =
    orbitRepresentativePattern descriptor504.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf504 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0179.pattern504 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0179.pattern504) descriptor504 checked504 (hRep descriptor504.representative)

def descriptor505 : OrbitDescriptor := ⟨12, 15, true⟩

theorem checked505 : orbitPatternTransform descriptor505 (Generated.Chunk0179.pattern505) =
    orbitRepresentativePattern descriptor505.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf505 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0179.pattern505 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0179.pattern505) descriptor505 checked505 (hRep descriptor505.representative)

def descriptor506 : OrbitDescriptor := ⟨11, 17, true⟩

theorem checked506 : orbitPatternTransform descriptor506 (Generated.Chunk0179.pattern506) =
    orbitRepresentativePattern descriptor506.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf506 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0179.pattern506 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0179.pattern506) descriptor506 checked506 (hRep descriptor506.representative)

def descriptor507 : OrbitDescriptor := ⟨6, 23, true⟩

theorem checked507 : orbitPatternTransform descriptor507 (Generated.Chunk0179.pattern507) =
    orbitRepresentativePattern descriptor507.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf507 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0179.pattern507 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0179.pattern507) descriptor507 checked507 (hRep descriptor507.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0179.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0179.regionContext := by
  apply Generated.FunctionalChunk0179.valid
  · exact leaf503 hRep
  · exact leaf504 hRep
  · exact leaf505 hRep
  · exact leaf506 hRep
  · exact leaf507 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0179

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0180
def descriptor508 : OrbitDescriptor := ⟨45, 18, false⟩

theorem checked508 : orbitPatternTransform descriptor508 (Generated.Chunk0180.pattern508) =
    orbitRepresentativePattern descriptor508.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf508 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0180.pattern508 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0180.pattern508) descriptor508 checked508 (hRep descriptor508.representative)

def descriptor509 : OrbitDescriptor := ⟨46, 18, false⟩

theorem checked509 : orbitPatternTransform descriptor509 (Generated.Chunk0180.pattern509) =
    orbitRepresentativePattern descriptor509.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf509 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0180.pattern509 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0180.pattern509) descriptor509 checked509 (hRep descriptor509.representative)

def descriptor510 : OrbitDescriptor := ⟨47, 18, false⟩

theorem checked510 : orbitPatternTransform descriptor510 (Generated.Chunk0180.pattern510) =
    orbitRepresentativePattern descriptor510.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf510 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0180.pattern510 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0180.pattern510) descriptor510 checked510 (hRep descriptor510.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0180.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0180.regionContext := by
  apply Generated.FunctionalChunk0180.valid
  · exact leaf508 hRep
  · exact leaf509 hRep
  · exact leaf510 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0180

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0181
def descriptor511 : OrbitDescriptor := ⟨49, 18, false⟩

theorem checked511 : orbitPatternTransform descriptor511 (Generated.Chunk0181.pattern511) =
    orbitRepresentativePattern descriptor511.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf511 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0181.pattern511 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0181.pattern511) descriptor511 checked511 (hRep descriptor511.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0181.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0181.regionContext := by
  apply Generated.FunctionalChunk0181.valid
  · exact leaf511 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0181

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0182
def descriptor512 : OrbitDescriptor := ⟨50, 4, false⟩

theorem checked512 : orbitPatternTransform descriptor512 (Generated.Chunk0182.pattern512) =
    orbitRepresentativePattern descriptor512.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf512 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0182.pattern512 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0182.pattern512) descriptor512 checked512 (hRep descriptor512.representative)

def descriptor513 : OrbitDescriptor := ⟨51, 4, false⟩

theorem checked513 : orbitPatternTransform descriptor513 (Generated.Chunk0182.pattern513) =
    orbitRepresentativePattern descriptor513.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf513 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0182.pattern513 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0182.pattern513) descriptor513 checked513 (hRep descriptor513.representative)

def descriptor514 : OrbitDescriptor := ⟨52, 4, false⟩

theorem checked514 : orbitPatternTransform descriptor514 (Generated.Chunk0182.pattern514) =
    orbitRepresentativePattern descriptor514.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf514 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0182.pattern514 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0182.pattern514) descriptor514 checked514 (hRep descriptor514.representative)

def descriptor515 : OrbitDescriptor := ⟨53, 4, false⟩

theorem checked515 : orbitPatternTransform descriptor515 (Generated.Chunk0182.pattern515) =
    orbitRepresentativePattern descriptor515.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf515 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0182.pattern515 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0182.pattern515) descriptor515 checked515 (hRep descriptor515.representative)

def descriptor516 : OrbitDescriptor := ⟨54, 4, false⟩

theorem checked516 : orbitPatternTransform descriptor516 (Generated.Chunk0182.pattern516) =
    orbitRepresentativePattern descriptor516.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf516 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0182.pattern516 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0182.pattern516) descriptor516 checked516 (hRep descriptor516.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0182.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0182.regionContext := by
  apply Generated.FunctionalChunk0182.valid
  · exact leaf512 hRep
  · exact leaf513 hRep
  · exact leaf514 hRep
  · exact leaf515 hRep
  · exact leaf516 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0182

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0183
def descriptor517 : OrbitDescriptor := ⟨60, 15, true⟩

theorem checked517 : orbitPatternTransform descriptor517 (Generated.Chunk0183.pattern517) =
    orbitRepresentativePattern descriptor517.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf517 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0183.pattern517 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0183.pattern517) descriptor517 checked517 (hRep descriptor517.representative)

def descriptor518 : OrbitDescriptor := ⟨59, 15, true⟩

theorem checked518 : orbitPatternTransform descriptor518 (Generated.Chunk0183.pattern518) =
    orbitRepresentativePattern descriptor518.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf518 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0183.pattern518 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0183.pattern518) descriptor518 checked518 (hRep descriptor518.representative)

def descriptor519 : OrbitDescriptor := ⟨58, 15, true⟩

theorem checked519 : orbitPatternTransform descriptor519 (Generated.Chunk0183.pattern519) =
    orbitRepresentativePattern descriptor519.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf519 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0183.pattern519 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0183.pattern519) descriptor519 checked519 (hRep descriptor519.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0183.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0183.regionContext := by
  apply Generated.FunctionalChunk0183.valid
  · exact leaf517 hRep
  · exact leaf518 hRep
  · exact leaf519 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0183
