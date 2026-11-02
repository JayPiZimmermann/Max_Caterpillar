import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0136
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0137
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0138
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0139
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0140
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0141
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0142
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0143
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0136
def descriptor382 : OrbitDescriptor := ⟨43, 3, false⟩

theorem checked382 : orbitPatternTransform descriptor382 (Generated.Chunk0136.pattern382) =
    orbitRepresentativePattern descriptor382.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf382 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0136.pattern382 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0136.pattern382) descriptor382 checked382 (hRep descriptor382.representative)

def descriptor383 : OrbitDescriptor := ⟨56, 2, false⟩

theorem checked383 : orbitPatternTransform descriptor383 (Generated.Chunk0136.pattern383) =
    orbitRepresentativePattern descriptor383.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf383 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0136.pattern383 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0136.pattern383) descriptor383 checked383 (hRep descriptor383.representative)

def descriptor384 : OrbitDescriptor := ⟨59, 2, false⟩

theorem checked384 : orbitPatternTransform descriptor384 (Generated.Chunk0136.pattern384) =
    orbitRepresentativePattern descriptor384.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf384 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0136.pattern384 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0136.pattern384) descriptor384 checked384 (hRep descriptor384.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0136.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0136.regionContext := by
  apply Generated.FunctionalChunk0136.valid
  · exact leaf382 hRep
  · exact leaf383 hRep
  · exact leaf384 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0136

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0137
def descriptor385 : OrbitDescriptor := ⟨44, 3, false⟩

theorem checked385 : orbitPatternTransform descriptor385 (Generated.Chunk0137.pattern385) =
    orbitRepresentativePattern descriptor385.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf385 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0137.pattern385 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0137.pattern385) descriptor385 checked385 (hRep descriptor385.representative)

def descriptor386 : OrbitDescriptor := ⟨57, 2, false⟩

theorem checked386 : orbitPatternTransform descriptor386 (Generated.Chunk0137.pattern386) =
    orbitRepresentativePattern descriptor386.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf386 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0137.pattern386 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0137.pattern386) descriptor386 checked386 (hRep descriptor386.representative)

def descriptor387 : OrbitDescriptor := ⟨60, 2, false⟩

theorem checked387 : orbitPatternTransform descriptor387 (Generated.Chunk0137.pattern387) =
    orbitRepresentativePattern descriptor387.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf387 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0137.pattern387 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0137.pattern387) descriptor387 checked387 (hRep descriptor387.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0137.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0137.regionContext := by
  apply Generated.FunctionalChunk0137.valid
  · exact leaf385 hRep
  · exact leaf386 hRep
  · exact leaf387 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0137

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0138
def descriptor388 : OrbitDescriptor := ⟨61, 2, false⟩

theorem checked388 : orbitPatternTransform descriptor388 (Generated.Chunk0138.pattern388) =
    orbitRepresentativePattern descriptor388.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf388 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0138.pattern388 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0138.pattern388) descriptor388 checked388 (hRep descriptor388.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0138.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0138.regionContext := by
  apply Generated.FunctionalChunk0138.valid
  · exact leaf388 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0138

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0139
def descriptor389 : OrbitDescriptor := ⟨60, 21, true⟩

theorem checked389 : orbitPatternTransform descriptor389 (Generated.Chunk0139.pattern389) =
    orbitRepresentativePattern descriptor389.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf389 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0139.pattern389 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0139.pattern389) descriptor389 checked389 (hRep descriptor389.representative)

def descriptor390 : OrbitDescriptor := ⟨59, 21, true⟩

theorem checked390 : orbitPatternTransform descriptor390 (Generated.Chunk0139.pattern390) =
    orbitRepresentativePattern descriptor390.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf390 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0139.pattern390 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0139.pattern390) descriptor390 checked390 (hRep descriptor390.representative)

def descriptor391 : OrbitDescriptor := ⟨58, 21, true⟩

theorem checked391 : orbitPatternTransform descriptor391 (Generated.Chunk0139.pattern391) =
    orbitRepresentativePattern descriptor391.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf391 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0139.pattern391 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0139.pattern391) descriptor391 checked391 (hRep descriptor391.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0139.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0139.regionContext := by
  apply Generated.FunctionalChunk0139.valid
  · exact leaf389 hRep
  · exact leaf390 hRep
  · exact leaf391 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0139

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0140
def descriptor392 : OrbitDescriptor := ⟨4, 5, false⟩

theorem checked392 : orbitPatternTransform descriptor392 (Generated.Chunk0140.pattern392) =
    orbitRepresentativePattern descriptor392.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf392 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0140.pattern392 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0140.pattern392) descriptor392 checked392 (hRep descriptor392.representative)

def descriptor393 : OrbitDescriptor := ⟨6, 5, false⟩

theorem checked393 : orbitPatternTransform descriptor393 (Generated.Chunk0140.pattern393) =
    orbitRepresentativePattern descriptor393.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf393 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0140.pattern393 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0140.pattern393) descriptor393 checked393 (hRep descriptor393.representative)

def descriptor394 : OrbitDescriptor := ⟨7, 3, false⟩

theorem checked394 : orbitPatternTransform descriptor394 (Generated.Chunk0140.pattern394) =
    orbitRepresentativePattern descriptor394.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf394 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0140.pattern394 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0140.pattern394) descriptor394 checked394 (hRep descriptor394.representative)

def descriptor395 : OrbitDescriptor := ⟨8, 3, false⟩

theorem checked395 : orbitPatternTransform descriptor395 (Generated.Chunk0140.pattern395) =
    orbitRepresentativePattern descriptor395.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf395 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0140.pattern395 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0140.pattern395) descriptor395 checked395 (hRep descriptor395.representative)

def descriptor396 : OrbitDescriptor := ⟨9, 3, false⟩

theorem checked396 : orbitPatternTransform descriptor396 (Generated.Chunk0140.pattern396) =
    orbitRepresentativePattern descriptor396.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf396 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0140.pattern396 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0140.pattern396) descriptor396 checked396 (hRep descriptor396.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0140.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0140.regionContext := by
  apply Generated.FunctionalChunk0140.valid
  · exact leaf392 hRep
  · exact leaf393 hRep
  · exact leaf394 hRep
  · exact leaf395 hRep
  · exact leaf396 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0140

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0141
def descriptor397 : OrbitDescriptor := ⟨30, 3, false⟩

theorem checked397 : orbitPatternTransform descriptor397 (Generated.Chunk0141.pattern397) =
    orbitRepresentativePattern descriptor397.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf397 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0141.pattern397 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0141.pattern397) descriptor397 checked397 (hRep descriptor397.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0141.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0141.regionContext := by
  apply Generated.FunctionalChunk0141.valid
  · exact leaf397 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0141

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0142
def descriptor398 : OrbitDescriptor := ⟨45, 3, false⟩

theorem checked398 : orbitPatternTransform descriptor398 (Generated.Chunk0142.pattern398) =
    orbitRepresentativePattern descriptor398.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf398 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0142.pattern398 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0142.pattern398) descriptor398 checked398 (hRep descriptor398.representative)

def descriptor399 : OrbitDescriptor := ⟨58, 3, false⟩

theorem checked399 : orbitPatternTransform descriptor399 (Generated.Chunk0142.pattern399) =
    orbitRepresentativePattern descriptor399.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf399 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0142.pattern399 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0142.pattern399) descriptor399 checked399 (hRep descriptor399.representative)

def descriptor400 : OrbitDescriptor := ⟨54, 11, true⟩

theorem checked400 : orbitPatternTransform descriptor400 (Generated.Chunk0142.pattern400) =
    orbitRepresentativePattern descriptor400.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf400 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0142.pattern400 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0142.pattern400) descriptor400 checked400 (hRep descriptor400.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0142.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0142.regionContext := by
  apply Generated.FunctionalChunk0142.valid
  · exact leaf398 hRep
  · exact leaf399 hRep
  · exact leaf400 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0142

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0143
def descriptor401 : OrbitDescriptor := ⟨46, 3, false⟩

theorem checked401 : orbitPatternTransform descriptor401 (Generated.Chunk0143.pattern401) =
    orbitRepresentativePattern descriptor401.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf401 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0143.pattern401 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0143.pattern401) descriptor401 checked401 (hRep descriptor401.representative)

def descriptor402 : OrbitDescriptor := ⟨59, 3, false⟩

theorem checked402 : orbitPatternTransform descriptor402 (Generated.Chunk0143.pattern402) =
    orbitRepresentativePattern descriptor402.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf402 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0143.pattern402 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0143.pattern402) descriptor402 checked402 (hRep descriptor402.representative)

def descriptor403 : OrbitDescriptor := ⟨53, 11, true⟩

theorem checked403 : orbitPatternTransform descriptor403 (Generated.Chunk0143.pattern403) =
    orbitRepresentativePattern descriptor403.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf403 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0143.pattern403 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0143.pattern403) descriptor403 checked403 (hRep descriptor403.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0143.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0143.regionContext := by
  apply Generated.FunctionalChunk0143.valid
  · exact leaf401 hRep
  · exact leaf402 hRep
  · exact leaf403 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0143
