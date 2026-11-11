import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0096
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0097
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0098
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0099
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0100
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0101
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0102
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0103
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0096
def descriptor266 : OrbitDescriptor := ⟨59, 16, true⟩

theorem checked266 : orbitPatternTransform descriptor266 (Generated.Chunk0096.pattern266) =
    orbitRepresentativePattern descriptor266.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf266 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0096.pattern266 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0096.pattern266) descriptor266 checked266 (hRep descriptor266.representative)

def descriptor267 : OrbitDescriptor := ⟨56, 16, true⟩

theorem checked267 : orbitPatternTransform descriptor267 (Generated.Chunk0096.pattern267) =
    orbitRepresentativePattern descriptor267.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf267 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0096.pattern267 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0096.pattern267) descriptor267 checked267 (hRep descriptor267.representative)

def descriptor268 : OrbitDescriptor := ⟨43, 17, true⟩

theorem checked268 : orbitPatternTransform descriptor268 (Generated.Chunk0096.pattern268) =
    orbitRepresentativePattern descriptor268.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf268 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0096.pattern268 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0096.pattern268) descriptor268 checked268 (hRep descriptor268.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0096.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0096.regionContext := by
  apply Generated.FunctionalChunk0096.valid
  · exact leaf266 hRep
  · exact leaf267 hRep
  · exact leaf268 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0096

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0097
def descriptor269 : OrbitDescriptor := ⟨46, 16, true⟩

theorem checked269 : orbitPatternTransform descriptor269 (Generated.Chunk0097.pattern269) =
    orbitRepresentativePattern descriptor269.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf269 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0097.pattern269 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0097.pattern269) descriptor269 checked269 (hRep descriptor269.representative)

def descriptor270 : OrbitDescriptor := ⟨43, 16, true⟩

theorem checked270 : orbitPatternTransform descriptor270 (Generated.Chunk0097.pattern270) =
    orbitRepresentativePattern descriptor270.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf270 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0097.pattern270 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0097.pattern270) descriptor270 checked270 (hRep descriptor270.representative)

def descriptor271 : OrbitDescriptor := ⟨40, 16, true⟩

theorem checked271 : orbitPatternTransform descriptor271 (Generated.Chunk0097.pattern271) =
    orbitRepresentativePattern descriptor271.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf271 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0097.pattern271 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0097.pattern271) descriptor271 checked271 (hRep descriptor271.representative)

def descriptor272 : OrbitDescriptor := ⟨39, 16, true⟩

theorem checked272 : orbitPatternTransform descriptor272 (Generated.Chunk0097.pattern272) =
    orbitRepresentativePattern descriptor272.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf272 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0097.pattern272 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0097.pattern272) descriptor272 checked272 (hRep descriptor272.representative)

def descriptor273 : OrbitDescriptor := ⟨37, 22, true⟩

theorem checked273 : orbitPatternTransform descriptor273 (Generated.Chunk0097.pattern273) =
    orbitRepresentativePattern descriptor273.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf273 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0097.pattern273 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0097.pattern273) descriptor273 checked273 (hRep descriptor273.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0097.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0097.regionContext := by
  apply Generated.FunctionalChunk0097.valid
  · exact leaf269 hRep
  · exact leaf270 hRep
  · exact leaf271 hRep
  · exact leaf272 hRep
  · exact leaf273 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0097

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0098
def descriptor274 : OrbitDescriptor := ⟨9, 18, false⟩

theorem checked274 : orbitPatternTransform descriptor274 (Generated.Chunk0098.pattern274) =
    orbitRepresentativePattern descriptor274.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf274 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0098.pattern274 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0098.pattern274) descriptor274 checked274 (hRep descriptor274.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0098.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0098.regionContext := by
  apply Generated.FunctionalChunk0098.valid
  · exact leaf274 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0098

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0099
def descriptor275 : OrbitDescriptor := ⟨14, 18, false⟩

theorem checked275 : orbitPatternTransform descriptor275 (Generated.Chunk0099.pattern275) =
    orbitRepresentativePattern descriptor275.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf275 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0099.pattern275 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0099.pattern275) descriptor275 checked275 (hRep descriptor275.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0099.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0099.regionContext := by
  apply Generated.FunctionalChunk0099.valid
  · exact leaf275 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0099

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0100
def descriptor276 : OrbitDescriptor := ⟨17, 18, false⟩

theorem checked276 : orbitPatternTransform descriptor276 (Generated.Chunk0100.pattern276) =
    orbitRepresentativePattern descriptor276.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf276 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0100.pattern276 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0100.pattern276) descriptor276 checked276 (hRep descriptor276.representative)

def descriptor277 : OrbitDescriptor := ⟨19, 18, false⟩

theorem checked277 : orbitPatternTransform descriptor277 (Generated.Chunk0100.pattern277) =
    orbitRepresentativePattern descriptor277.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf277 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0100.pattern277 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0100.pattern277) descriptor277 checked277 (hRep descriptor277.representative)

def descriptor278 : OrbitDescriptor := ⟨20, 4, false⟩

theorem checked278 : orbitPatternTransform descriptor278 (Generated.Chunk0100.pattern278) =
    orbitRepresentativePattern descriptor278.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf278 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0100.pattern278 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0100.pattern278) descriptor278 checked278 (hRep descriptor278.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0100.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0100.regionContext := by
  apply Generated.FunctionalChunk0100.valid
  · exact leaf276 hRep
  · exact leaf277 hRep
  · exact leaf278 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0100

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0101
def descriptor279 : OrbitDescriptor := ⟨19, 20, false⟩

theorem checked279 : orbitPatternTransform descriptor279 (Generated.Chunk0101.pattern279) =
    orbitRepresentativePattern descriptor279.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf279 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0101.pattern279 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0101.pattern279) descriptor279 checked279 (hRep descriptor279.representative)

def descriptor280 : OrbitDescriptor := ⟨22, 18, false⟩

theorem checked280 : orbitPatternTransform descriptor280 (Generated.Chunk0101.pattern280) =
    orbitRepresentativePattern descriptor280.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf280 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0101.pattern280 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0101.pattern280) descriptor280 checked280 (hRep descriptor280.representative)

def descriptor281 : OrbitDescriptor := ⟨23, 4, false⟩

theorem checked281 : orbitPatternTransform descriptor281 (Generated.Chunk0101.pattern281) =
    orbitRepresentativePattern descriptor281.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf281 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0101.pattern281 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0101.pattern281) descriptor281 checked281 (hRep descriptor281.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0101.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0101.regionContext := by
  apply Generated.FunctionalChunk0101.valid
  · exact leaf279 hRep
  · exact leaf280 hRep
  · exact leaf281 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0101

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0102
def descriptor282 : OrbitDescriptor := ⟨20, 10, false⟩

theorem checked282 : orbitPatternTransform descriptor282 (Generated.Chunk0102.pattern282) =
    orbitRepresentativePattern descriptor282.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf282 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0102.pattern282 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0102.pattern282) descriptor282 checked282 (hRep descriptor282.representative)

def descriptor283 : OrbitDescriptor := ⟨23, 10, false⟩

theorem checked283 : orbitPatternTransform descriptor283 (Generated.Chunk0102.pattern283) =
    orbitRepresentativePattern descriptor283.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf283 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0102.pattern283 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0102.pattern283) descriptor283 checked283 (hRep descriptor283.representative)

def descriptor284 : OrbitDescriptor := ⟨24, 1, false⟩

theorem checked284 : orbitPatternTransform descriptor284 (Generated.Chunk0102.pattern284) =
    orbitRepresentativePattern descriptor284.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf284 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0102.pattern284 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0102.pattern284) descriptor284 checked284 (hRep descriptor284.representative)

def descriptor285 : OrbitDescriptor := ⟨25, 1, false⟩

theorem checked285 : orbitPatternTransform descriptor285 (Generated.Chunk0102.pattern285) =
    orbitRepresentativePattern descriptor285.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf285 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0102.pattern285 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0102.pattern285) descriptor285 checked285 (hRep descriptor285.representative)

def descriptor286 : OrbitDescriptor := ⟨26, 1, false⟩

theorem checked286 : orbitPatternTransform descriptor286 (Generated.Chunk0102.pattern286) =
    orbitRepresentativePattern descriptor286.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf286 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0102.pattern286 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0102.pattern286) descriptor286 checked286 (hRep descriptor286.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0102.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0102.regionContext := by
  apply Generated.FunctionalChunk0102.valid
  · exact leaf282 hRep
  · exact leaf283 hRep
  · exact leaf284 hRep
  · exact leaf285 hRep
  · exact leaf286 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0102

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0103
def descriptor287 : OrbitDescriptor := ⟨35, 1, false⟩

theorem checked287 : orbitPatternTransform descriptor287 (Generated.Chunk0103.pattern287) =
    orbitRepresentativePattern descriptor287.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf287 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0103.pattern287 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0103.pattern287) descriptor287 checked287 (hRep descriptor287.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0103.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0103.regionContext := by
  apply Generated.FunctionalChunk0103.valid
  · exact leaf287 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0103
