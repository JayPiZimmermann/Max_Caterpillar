import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0080
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0081
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0082
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0083
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0084
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0085
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0086
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0087
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0080
def descriptor226 : OrbitDescriptor := ⟨7, 18, false⟩

theorem checked226 : orbitPatternTransform descriptor226 (Generated.Chunk0080.pattern226) =
    orbitRepresentativePattern descriptor226.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf226 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0080.pattern226 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0080.pattern226) descriptor226 checked226 (hRep descriptor226.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0080.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0080.regionContext := by
  apply Generated.FunctionalChunk0080.valid
  · exact leaf226 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0080

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0081
def descriptor227 : OrbitDescriptor := ⟨12, 18, false⟩

theorem checked227 : orbitPatternTransform descriptor227 (Generated.Chunk0081.pattern227) =
    orbitRepresentativePattern descriptor227.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf227 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0081.pattern227 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0081.pattern227) descriptor227 checked227 (hRep descriptor227.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0081.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0081.regionContext := by
  apply Generated.FunctionalChunk0081.valid
  · exact leaf227 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0081

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0082
def descriptor228 : OrbitDescriptor := ⟨15, 1, false⟩

theorem checked228 : orbitPatternTransform descriptor228 (Generated.Chunk0082.pattern228) =
    orbitRepresentativePattern descriptor228.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf228 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0082.pattern228 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0082.pattern228) descriptor228 checked228 (hRep descriptor228.representative)

def descriptor229 : OrbitDescriptor := ⟨16, 1, false⟩

theorem checked229 : orbitPatternTransform descriptor229 (Generated.Chunk0082.pattern229) =
    orbitRepresentativePattern descriptor229.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf229 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0082.pattern229 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0082.pattern229) descriptor229 checked229 (hRep descriptor229.representative)

def descriptor230 : OrbitDescriptor := ⟨17, 1, false⟩

theorem checked230 : orbitPatternTransform descriptor230 (Generated.Chunk0082.pattern230) =
    orbitRepresentativePattern descriptor230.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf230 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0082.pattern230 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0082.pattern230) descriptor230 checked230 (hRep descriptor230.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0082.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0082.regionContext := by
  apply Generated.FunctionalChunk0082.valid
  · exact leaf228 hRep
  · exact leaf229 hRep
  · exact leaf230 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0082

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0083
def descriptor231 : OrbitDescriptor := ⟨16, 7, false⟩

theorem checked231 : orbitPatternTransform descriptor231 (Generated.Chunk0083.pattern231) =
    orbitRepresentativePattern descriptor231.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf231 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0083.pattern231 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0083.pattern231) descriptor231 checked231 (hRep descriptor231.representative)

def descriptor232 : OrbitDescriptor := ⟨18, 1, false⟩

theorem checked232 : orbitPatternTransform descriptor232 (Generated.Chunk0083.pattern232) =
    orbitRepresentativePattern descriptor232.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf232 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0083.pattern232 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0083.pattern232) descriptor232 checked232 (hRep descriptor232.representative)

def descriptor233 : OrbitDescriptor := ⟨19, 1, false⟩

theorem checked233 : orbitPatternTransform descriptor233 (Generated.Chunk0083.pattern233) =
    orbitRepresentativePattern descriptor233.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf233 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0083.pattern233 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0083.pattern233) descriptor233 checked233 (hRep descriptor233.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0083.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0083.regionContext := by
  apply Generated.FunctionalChunk0083.valid
  · exact leaf231 hRep
  · exact leaf232 hRep
  · exact leaf233 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0083

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0084
def descriptor234 : OrbitDescriptor := ⟨17, 7, false⟩

theorem checked234 : orbitPatternTransform descriptor234 (Generated.Chunk0084.pattern234) =
    orbitRepresentativePattern descriptor234.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf234 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0084.pattern234 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0084.pattern234) descriptor234 checked234 (hRep descriptor234.representative)

def descriptor235 : OrbitDescriptor := ⟨19, 7, false⟩

theorem checked235 : orbitPatternTransform descriptor235 (Generated.Chunk0084.pattern235) =
    orbitRepresentativePattern descriptor235.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf235 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0084.pattern235 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0084.pattern235) descriptor235 checked235 (hRep descriptor235.representative)

def descriptor236 : OrbitDescriptor := ⟨20, 1, false⟩

theorem checked236 : orbitPatternTransform descriptor236 (Generated.Chunk0084.pattern236) =
    orbitRepresentativePattern descriptor236.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf236 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0084.pattern236 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0084.pattern236) descriptor236 checked236 (hRep descriptor236.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0084.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0084.regionContext := by
  apply Generated.FunctionalChunk0084.valid
  · exact leaf234 hRep
  · exact leaf235 hRep
  · exact leaf236 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0084

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0085
def descriptor237 : OrbitDescriptor := ⟨33, 1, false⟩

theorem checked237 : orbitPatternTransform descriptor237 (Generated.Chunk0085.pattern237) =
    orbitRepresentativePattern descriptor237.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf237 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0085.pattern237 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0085.pattern237) descriptor237 checked237 (hRep descriptor237.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0085.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0085.regionContext := by
  apply Generated.FunctionalChunk0085.valid
  · exact leaf237 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0085

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0086
def descriptor238 : OrbitDescriptor := ⟨50, 1, false⟩

theorem checked238 : orbitPatternTransform descriptor238 (Generated.Chunk0086.pattern238) =
    orbitRepresentativePattern descriptor238.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf238 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0086.pattern238 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0086.pattern238) descriptor238 checked238 (hRep descriptor238.representative)

def descriptor239 : OrbitDescriptor := ⟨51, 1, false⟩

theorem checked239 : orbitPatternTransform descriptor239 (Generated.Chunk0086.pattern239) =
    orbitRepresentativePattern descriptor239.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf239 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0086.pattern239 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0086.pattern239) descriptor239 checked239 (hRep descriptor239.representative)

def descriptor240 : OrbitDescriptor := ⟨52, 1, false⟩

theorem checked240 : orbitPatternTransform descriptor240 (Generated.Chunk0086.pattern240) =
    orbitRepresentativePattern descriptor240.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf240 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0086.pattern240 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0086.pattern240) descriptor240 checked240 (hRep descriptor240.representative)

def descriptor241 : OrbitDescriptor := ⟨60, 17, true⟩

theorem checked241 : orbitPatternTransform descriptor241 (Generated.Chunk0086.pattern241) =
    orbitRepresentativePattern descriptor241.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf241 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0086.pattern241 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0086.pattern241) descriptor241 checked241 (hRep descriptor241.representative)

def descriptor242 : OrbitDescriptor := ⟨47, 17, true⟩

theorem checked242 : orbitPatternTransform descriptor242 (Generated.Chunk0086.pattern242) =
    orbitRepresentativePattern descriptor242.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf242 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0086.pattern242 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0086.pattern242) descriptor242 checked242 (hRep descriptor242.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0086.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0086.regionContext := by
  apply Generated.FunctionalChunk0086.valid
  · exact leaf238 hRep
  · exact leaf239 hRep
  · exact leaf240 hRep
  · exact leaf241 hRep
  · exact leaf242 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0086

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0087
def descriptor243 : OrbitDescriptor := ⟨60, 16, true⟩

theorem checked243 : orbitPatternTransform descriptor243 (Generated.Chunk0087.pattern243) =
    orbitRepresentativePattern descriptor243.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf243 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0087.pattern243 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0087.pattern243) descriptor243 checked243 (hRep descriptor243.representative)

def descriptor244 : OrbitDescriptor := ⟨57, 16, true⟩

theorem checked244 : orbitPatternTransform descriptor244 (Generated.Chunk0087.pattern244) =
    orbitRepresentativePattern descriptor244.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf244 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0087.pattern244 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0087.pattern244) descriptor244 checked244 (hRep descriptor244.representative)

def descriptor245 : OrbitDescriptor := ⟨44, 17, true⟩

theorem checked245 : orbitPatternTransform descriptor245 (Generated.Chunk0087.pattern245) =
    orbitRepresentativePattern descriptor245.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf245 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0087.pattern245 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0087.pattern245) descriptor245 checked245 (hRep descriptor245.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0087.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0087.regionContext := by
  apply Generated.FunctionalChunk0087.valid
  · exact leaf243 hRep
  · exact leaf244 hRep
  · exact leaf245 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0087
