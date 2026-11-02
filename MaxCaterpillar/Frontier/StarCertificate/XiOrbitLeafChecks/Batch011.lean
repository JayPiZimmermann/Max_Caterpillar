import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0088
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0089
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0090
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0091
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0092
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0093
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0094
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0095
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0088
def descriptor246 : OrbitDescriptor := ⟨47, 16, true⟩

theorem checked246 : orbitPatternTransform descriptor246 (Generated.Chunk0088.pattern246) =
    orbitRepresentativePattern descriptor246.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf246 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0088.pattern246 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0088.pattern246) descriptor246 checked246 (hRep descriptor246.representative)

def descriptor247 : OrbitDescriptor := ⟨44, 16, true⟩

theorem checked247 : orbitPatternTransform descriptor247 (Generated.Chunk0088.pattern247) =
    orbitRepresentativePattern descriptor247.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf247 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0088.pattern247 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0088.pattern247) descriptor247 checked247 (hRep descriptor247.representative)

def descriptor248 : OrbitDescriptor := ⟨41, 16, true⟩

theorem checked248 : orbitPatternTransform descriptor248 (Generated.Chunk0088.pattern248) =
    orbitRepresentativePattern descriptor248.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf248 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0088.pattern248 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0088.pattern248) descriptor248 checked248 (hRep descriptor248.representative)

def descriptor249 : OrbitDescriptor := ⟨40, 22, true⟩

theorem checked249 : orbitPatternTransform descriptor249 (Generated.Chunk0088.pattern249) =
    orbitRepresentativePattern descriptor249.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf249 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0088.pattern249 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0088.pattern249) descriptor249 checked249 (hRep descriptor249.representative)

def descriptor250 : OrbitDescriptor := ⟨38, 22, true⟩

theorem checked250 : orbitPatternTransform descriptor250 (Generated.Chunk0088.pattern250) =
    orbitRepresentativePattern descriptor250.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf250 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0088.pattern250 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0088.pattern250) descriptor250 checked250 (hRep descriptor250.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0088.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0088.regionContext := by
  apply Generated.FunctionalChunk0088.valid
  · exact leaf246 hRep
  · exact leaf247 hRep
  · exact leaf248 hRep
  · exact leaf249 hRep
  · exact leaf250 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0088

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0089
def descriptor251 : OrbitDescriptor := ⟨8, 18, false⟩

theorem checked251 : orbitPatternTransform descriptor251 (Generated.Chunk0089.pattern251) =
    orbitRepresentativePattern descriptor251.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf251 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0089.pattern251 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0089.pattern251) descriptor251 checked251 (hRep descriptor251.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0089.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0089.regionContext := by
  apply Generated.FunctionalChunk0089.valid
  · exact leaf251 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0089

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0090
def descriptor252 : OrbitDescriptor := ⟨13, 18, false⟩

theorem checked252 : orbitPatternTransform descriptor252 (Generated.Chunk0090.pattern252) =
    orbitRepresentativePattern descriptor252.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf252 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0090.pattern252 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0090.pattern252) descriptor252 checked252 (hRep descriptor252.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0090.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0090.regionContext := by
  apply Generated.FunctionalChunk0090.valid
  · exact leaf252 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0090

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0091
def descriptor253 : OrbitDescriptor := ⟨16, 18, false⟩

theorem checked253 : orbitPatternTransform descriptor253 (Generated.Chunk0091.pattern253) =
    orbitRepresentativePattern descriptor253.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf253 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0091.pattern253 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0091.pattern253) descriptor253 checked253 (hRep descriptor253.representative)

def descriptor254 : OrbitDescriptor := ⟨18, 4, false⟩

theorem checked254 : orbitPatternTransform descriptor254 (Generated.Chunk0091.pattern254) =
    orbitRepresentativePattern descriptor254.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf254 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0091.pattern254 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0091.pattern254) descriptor254 checked254 (hRep descriptor254.representative)

def descriptor255 : OrbitDescriptor := ⟨19, 4, false⟩

theorem checked255 : orbitPatternTransform descriptor255 (Generated.Chunk0091.pattern255) =
    orbitRepresentativePattern descriptor255.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf255 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0091.pattern255 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0091.pattern255) descriptor255 checked255 (hRep descriptor255.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0091.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0091.regionContext := by
  apply Generated.FunctionalChunk0091.valid
  · exact leaf253 hRep
  · exact leaf254 hRep
  · exact leaf255 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0091

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0092
def descriptor256 : OrbitDescriptor := ⟨18, 10, false⟩

theorem checked256 : orbitPatternTransform descriptor256 (Generated.Chunk0092.pattern256) =
    orbitRepresentativePattern descriptor256.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf256 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0092.pattern256 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0092.pattern256) descriptor256 checked256 (hRep descriptor256.representative)

def descriptor257 : OrbitDescriptor := ⟨21, 1, false⟩

theorem checked257 : orbitPatternTransform descriptor257 (Generated.Chunk0092.pattern257) =
    orbitRepresentativePattern descriptor257.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf257 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0092.pattern257 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0092.pattern257) descriptor257 checked257 (hRep descriptor257.representative)

def descriptor258 : OrbitDescriptor := ⟨22, 1, false⟩

theorem checked258 : orbitPatternTransform descriptor258 (Generated.Chunk0092.pattern258) =
    orbitRepresentativePattern descriptor258.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf258 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0092.pattern258 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0092.pattern258) descriptor258 checked258 (hRep descriptor258.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0092.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0092.regionContext := by
  apply Generated.FunctionalChunk0092.valid
  · exact leaf256 hRep
  · exact leaf257 hRep
  · exact leaf258 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0092

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0093
def descriptor259 : OrbitDescriptor := ⟨19, 10, false⟩

theorem checked259 : orbitPatternTransform descriptor259 (Generated.Chunk0093.pattern259) =
    orbitRepresentativePattern descriptor259.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf259 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0093.pattern259 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0093.pattern259) descriptor259 checked259 (hRep descriptor259.representative)

def descriptor260 : OrbitDescriptor := ⟨22, 7, false⟩

theorem checked260 : orbitPatternTransform descriptor260 (Generated.Chunk0093.pattern260) =
    orbitRepresentativePattern descriptor260.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf260 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0093.pattern260 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0093.pattern260) descriptor260 checked260 (hRep descriptor260.representative)

def descriptor261 : OrbitDescriptor := ⟨23, 1, false⟩

theorem checked261 : orbitPatternTransform descriptor261 (Generated.Chunk0093.pattern261) =
    orbitRepresentativePattern descriptor261.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf261 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0093.pattern261 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0093.pattern261) descriptor261 checked261 (hRep descriptor261.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0093.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0093.regionContext := by
  apply Generated.FunctionalChunk0093.valid
  · exact leaf259 hRep
  · exact leaf260 hRep
  · exact leaf261 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0093

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0094
def descriptor262 : OrbitDescriptor := ⟨34, 1, false⟩

theorem checked262 : orbitPatternTransform descriptor262 (Generated.Chunk0094.pattern262) =
    orbitRepresentativePattern descriptor262.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf262 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0094.pattern262 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0094.pattern262) descriptor262 checked262 (hRep descriptor262.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0094.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0094.regionContext := by
  apply Generated.FunctionalChunk0094.valid
  · exact leaf262 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0094

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0095
def descriptor263 : OrbitDescriptor := ⟨53, 1, false⟩

theorem checked263 : orbitPatternTransform descriptor263 (Generated.Chunk0095.pattern263) =
    orbitRepresentativePattern descriptor263.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf263 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0095.pattern263 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0095.pattern263) descriptor263 checked263 (hRep descriptor263.representative)

def descriptor264 : OrbitDescriptor := ⟨59, 17, true⟩

theorem checked264 : orbitPatternTransform descriptor264 (Generated.Chunk0095.pattern264) =
    orbitRepresentativePattern descriptor264.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf264 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0095.pattern264 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0095.pattern264) descriptor264 checked264 (hRep descriptor264.representative)

def descriptor265 : OrbitDescriptor := ⟨46, 17, true⟩

theorem checked265 : orbitPatternTransform descriptor265 (Generated.Chunk0095.pattern265) =
    orbitRepresentativePattern descriptor265.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf265 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0095.pattern265 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0095.pattern265) descriptor265 checked265 (hRep descriptor265.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0095.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0095.regionContext := by
  apply Generated.FunctionalChunk0095.valid
  · exact leaf263 hRep
  · exact leaf264 hRep
  · exact leaf265 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0095
