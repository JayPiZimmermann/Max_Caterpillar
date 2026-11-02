import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0160
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0161
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0162
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0163
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0164
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0165
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0166
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0167
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0160
def descriptor452 : OrbitDescriptor := ⟨43, 5, false⟩

theorem checked452 : orbitPatternTransform descriptor452 (Generated.Chunk0160.pattern452) =
    orbitRepresentativePattern descriptor452.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf452 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0160.pattern452 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0160.pattern452) descriptor452 checked452 (hRep descriptor452.representative)

def descriptor453 : OrbitDescriptor := ⟨56, 4, false⟩

theorem checked453 : orbitPatternTransform descriptor453 (Generated.Chunk0160.pattern453) =
    orbitRepresentativePattern descriptor453.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf453 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0160.pattern453 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0160.pattern453) descriptor453 checked453 (hRep descriptor453.representative)

def descriptor454 : OrbitDescriptor := ⟨59, 4, false⟩

theorem checked454 : orbitPatternTransform descriptor454 (Generated.Chunk0160.pattern454) =
    orbitRepresentativePattern descriptor454.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf454 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0160.pattern454 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0160.pattern454) descriptor454 checked454 (hRep descriptor454.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0160.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0160.regionContext := by
  apply Generated.FunctionalChunk0160.valid
  · exact leaf452 hRep
  · exact leaf453 hRep
  · exact leaf454 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0160

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0161
def descriptor455 : OrbitDescriptor := ⟨46, 5, false⟩

theorem checked455 : orbitPatternTransform descriptor455 (Generated.Chunk0161.pattern455) =
    orbitRepresentativePattern descriptor455.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf455 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0161.pattern455 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0161.pattern455) descriptor455 checked455 (hRep descriptor455.representative)

def descriptor456 : OrbitDescriptor := ⟨59, 5, false⟩

theorem checked456 : orbitPatternTransform descriptor456 (Generated.Chunk0161.pattern456) =
    orbitRepresentativePattern descriptor456.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf456 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0161.pattern456 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0161.pattern456) descriptor456 checked456 (hRep descriptor456.representative)

def descriptor457 : OrbitDescriptor := ⟨53, 9, true⟩

theorem checked457 : orbitPatternTransform descriptor457 (Generated.Chunk0161.pattern457) =
    orbitRepresentativePattern descriptor457.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf457 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0161.pattern457 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0161.pattern457) descriptor457 checked457 (hRep descriptor457.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0161.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0161.regionContext := by
  apply Generated.FunctionalChunk0161.valid
  · exact leaf455 hRep
  · exact leaf456 hRep
  · exact leaf457 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0161

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0162
def descriptor458 : OrbitDescriptor := ⟨34, 9, true⟩

theorem checked458 : orbitPatternTransform descriptor458 (Generated.Chunk0162.pattern458) =
    orbitRepresentativePattern descriptor458.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf458 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0162.pattern458 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0162.pattern458) descriptor458 checked458 (hRep descriptor458.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0162.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0162.regionContext := by
  apply Generated.FunctionalChunk0162.valid
  · exact leaf458 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0162

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0163
def descriptor459 : OrbitDescriptor := ⟨23, 9, true⟩

theorem checked459 : orbitPatternTransform descriptor459 (Generated.Chunk0163.pattern459) =
    orbitRepresentativePattern descriptor459.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf459 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0163.pattern459 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0163.pattern459) descriptor459 checked459 (hRep descriptor459.representative)

def descriptor460 : OrbitDescriptor := ⟨22, 15, true⟩

theorem checked460 : orbitPatternTransform descriptor460 (Generated.Chunk0163.pattern460) =
    orbitRepresentativePattern descriptor460.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf460 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0163.pattern460 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0163.pattern460) descriptor460 checked460 (hRep descriptor460.representative)

def descriptor461 : OrbitDescriptor := ⟨19, 17, true⟩

theorem checked461 : orbitPatternTransform descriptor461 (Generated.Chunk0163.pattern461) =
    orbitRepresentativePattern descriptor461.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf461 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0163.pattern461 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0163.pattern461) descriptor461 checked461 (hRep descriptor461.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0163.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0163.regionContext := by
  apply Generated.FunctionalChunk0163.valid
  · exact leaf459 hRep
  · exact leaf460 hRep
  · exact leaf461 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0163

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0164
def descriptor462 : OrbitDescriptor := ⟨22, 9, true⟩

theorem checked462 : orbitPatternTransform descriptor462 (Generated.Chunk0164.pattern462) =
    orbitRepresentativePattern descriptor462.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf462 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0164.pattern462 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0164.pattern462) descriptor462 checked462 (hRep descriptor462.representative)

def descriptor463 : OrbitDescriptor := ⟨21, 9, true⟩

theorem checked463 : orbitPatternTransform descriptor463 (Generated.Chunk0164.pattern463) =
    orbitRepresentativePattern descriptor463.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf463 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0164.pattern463 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0164.pattern463) descriptor463 checked463 (hRep descriptor463.representative)

def descriptor464 : OrbitDescriptor := ⟨18, 17, true⟩

theorem checked464 : orbitPatternTransform descriptor464 (Generated.Chunk0164.pattern464) =
    orbitRepresentativePattern descriptor464.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf464 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0164.pattern464 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0164.pattern464) descriptor464 checked464 (hRep descriptor464.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0164.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0164.regionContext := by
  apply Generated.FunctionalChunk0164.valid
  · exact leaf462 hRep
  · exact leaf463 hRep
  · exact leaf464 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0164

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0165
def descriptor465 : OrbitDescriptor := ⟨19, 11, true⟩

theorem checked465 : orbitPatternTransform descriptor465 (Generated.Chunk0165.pattern465) =
    orbitRepresentativePattern descriptor465.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf465 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0165.pattern465 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0165.pattern465) descriptor465 checked465 (hRep descriptor465.representative)

def descriptor466 : OrbitDescriptor := ⟨18, 11, true⟩

theorem checked466 : orbitPatternTransform descriptor466 (Generated.Chunk0165.pattern466) =
    orbitRepresentativePattern descriptor466.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf466 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0165.pattern466 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0165.pattern466) descriptor466 checked466 (hRep descriptor466.representative)

def descriptor467 : OrbitDescriptor := ⟨16, 21, true⟩

theorem checked467 : orbitPatternTransform descriptor467 (Generated.Chunk0165.pattern467) =
    orbitRepresentativePattern descriptor467.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf467 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0165.pattern467 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0165.pattern467) descriptor467 checked467 (hRep descriptor467.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0165.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0165.regionContext := by
  apply Generated.FunctionalChunk0165.valid
  · exact leaf465 hRep
  · exact leaf466 hRep
  · exact leaf467 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0165

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0166
def descriptor468 : OrbitDescriptor := ⟨13, 21, true⟩

theorem checked468 : orbitPatternTransform descriptor468 (Generated.Chunk0166.pattern468) =
    orbitRepresentativePattern descriptor468.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf468 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0166.pattern468 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0166.pattern468) descriptor468 checked468 (hRep descriptor468.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0166.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0166.regionContext := by
  apply Generated.FunctionalChunk0166.valid
  · exact leaf468 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0166

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0167
def descriptor469 : OrbitDescriptor := ⟨8, 21, true⟩

theorem checked469 : orbitPatternTransform descriptor469 (Generated.Chunk0167.pattern469) =
    orbitRepresentativePattern descriptor469.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf469 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0167.pattern469 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0167.pattern469) descriptor469 checked469 (hRep descriptor469.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0167.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0167.regionContext := by
  apply Generated.FunctionalChunk0167.valid
  · exact leaf469 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0167
