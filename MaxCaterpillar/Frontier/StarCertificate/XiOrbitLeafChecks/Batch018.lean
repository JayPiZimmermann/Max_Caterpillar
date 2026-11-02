import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0144
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0145
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0146
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0147
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0148
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0149
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0150
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0151
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0144
def descriptor404 : OrbitDescriptor := ⟨47, 3, false⟩

theorem checked404 : orbitPatternTransform descriptor404 (Generated.Chunk0144.pattern404) =
    orbitRepresentativePattern descriptor404.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf404 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0144.pattern404 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0144.pattern404) descriptor404 checked404 (hRep descriptor404.representative)

def descriptor405 : OrbitDescriptor := ⟨60, 3, false⟩

theorem checked405 : orbitPatternTransform descriptor405 (Generated.Chunk0144.pattern405) =
    orbitRepresentativePattern descriptor405.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf405 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0144.pattern405 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0144.pattern405) descriptor405 checked405 (hRep descriptor405.representative)

def descriptor406 : OrbitDescriptor := ⟨52, 11, true⟩

theorem checked406 : orbitPatternTransform descriptor406 (Generated.Chunk0144.pattern406) =
    orbitRepresentativePattern descriptor406.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf406 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0144.pattern406 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0144.pattern406) descriptor406 checked406 (hRep descriptor406.representative)

def descriptor407 : OrbitDescriptor := ⟨51, 11, true⟩

theorem checked407 : orbitPatternTransform descriptor407 (Generated.Chunk0144.pattern407) =
    orbitRepresentativePattern descriptor407.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf407 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0144.pattern407 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0144.pattern407) descriptor407 checked407 (hRep descriptor407.representative)

def descriptor408 : OrbitDescriptor := ⟨50, 11, true⟩

theorem checked408 : orbitPatternTransform descriptor408 (Generated.Chunk0144.pattern408) =
    orbitRepresentativePattern descriptor408.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf408 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0144.pattern408 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0144.pattern408) descriptor408 checked408 (hRep descriptor408.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0144.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0144.regionContext := by
  apply Generated.FunctionalChunk0144.valid
  · exact leaf404 hRep
  · exact leaf405 hRep
  · exact leaf406 hRep
  · exact leaf407 hRep
  · exact leaf408 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0144

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0145
def descriptor409 : OrbitDescriptor := ⟨49, 21, true⟩

theorem checked409 : orbitPatternTransform descriptor409 (Generated.Chunk0145.pattern409) =
    orbitRepresentativePattern descriptor409.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf409 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0145.pattern409 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0145.pattern409) descriptor409 checked409 (hRep descriptor409.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0145.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0145.regionContext := by
  apply Generated.FunctionalChunk0145.valid
  · exact leaf409 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0145

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0146
def descriptor410 : OrbitDescriptor := ⟨47, 21, true⟩

theorem checked410 : orbitPatternTransform descriptor410 (Generated.Chunk0146.pattern410) =
    orbitRepresentativePattern descriptor410.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf410 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0146.pattern410 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0146.pattern410) descriptor410 checked410 (hRep descriptor410.representative)

def descriptor411 : OrbitDescriptor := ⟨46, 21, true⟩

theorem checked411 : orbitPatternTransform descriptor411 (Generated.Chunk0146.pattern411) =
    orbitRepresentativePattern descriptor411.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf411 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0146.pattern411 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0146.pattern411) descriptor411 checked411 (hRep descriptor411.representative)

def descriptor412 : OrbitDescriptor := ⟨45, 21, true⟩

theorem checked412 : orbitPatternTransform descriptor412 (Generated.Chunk0146.pattern412) =
    orbitRepresentativePattern descriptor412.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf412 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0146.pattern412 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0146.pattern412) descriptor412 checked412 (hRep descriptor412.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0146.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0146.regionContext := by
  apply Generated.FunctionalChunk0146.valid
  · exact leaf410 hRep
  · exact leaf411 hRep
  · exact leaf412 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0146

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0147
def descriptor413 : OrbitDescriptor := ⟨28, 5, false⟩

theorem checked413 : orbitPatternTransform descriptor413 (Generated.Chunk0147.pattern413) =
    orbitRepresentativePattern descriptor413.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf413 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0147.pattern413 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0147.pattern413) descriptor413 checked413 (hRep descriptor413.representative)

def descriptor414 : OrbitDescriptor := ⟨29, 5, false⟩

theorem checked414 : orbitPatternTransform descriptor414 (Generated.Chunk0147.pattern414) =
    orbitRepresentativePattern descriptor414.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf414 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0147.pattern414 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0147.pattern414) descriptor414 checked414 (hRep descriptor414.representative)

def descriptor415 : OrbitDescriptor := ⟨30, 5, false⟩

theorem checked415 : orbitPatternTransform descriptor415 (Generated.Chunk0147.pattern415) =
    orbitRepresentativePattern descriptor415.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf415 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0147.pattern415 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0147.pattern415) descriptor415 checked415 (hRep descriptor415.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0147.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0147.regionContext := by
  apply Generated.FunctionalChunk0147.valid
  · exact leaf413 hRep
  · exact leaf414 hRep
  · exact leaf415 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0147

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0148
def descriptor416 : OrbitDescriptor := ⟨64, 3, false⟩

theorem checked416 : orbitPatternTransform descriptor416 (Generated.Chunk0148.pattern416) =
    orbitRepresentativePattern descriptor416.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf416 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0148.pattern416 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0148.pattern416) descriptor416 checked416 (hRep descriptor416.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0148.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0148.regionContext := by
  apply Generated.FunctionalChunk0148.valid
  · exact leaf416 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0148

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0149
def descriptor417 : OrbitDescriptor := ⟨35, 11, true⟩

theorem checked417 : orbitPatternTransform descriptor417 (Generated.Chunk0149.pattern417) =
    orbitRepresentativePattern descriptor417.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf417 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0149.pattern417 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0149.pattern417) descriptor417 checked417 (hRep descriptor417.representative)

def descriptor418 : OrbitDescriptor := ⟨34, 11, true⟩

theorem checked418 : orbitPatternTransform descriptor418 (Generated.Chunk0149.pattern418) =
    orbitRepresentativePattern descriptor418.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf418 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0149.pattern418 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0149.pattern418) descriptor418 checked418 (hRep descriptor418.representative)

def descriptor419 : OrbitDescriptor := ⟨33, 11, true⟩

theorem checked419 : orbitPatternTransform descriptor419 (Generated.Chunk0149.pattern419) =
    orbitRepresentativePattern descriptor419.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf419 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0149.pattern419 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0149.pattern419) descriptor419 checked419 (hRep descriptor419.representative)

def descriptor420 : OrbitDescriptor := ⟨32, 21, true⟩

theorem checked420 : orbitPatternTransform descriptor420 (Generated.Chunk0149.pattern420) =
    orbitRepresentativePattern descriptor420.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf420 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0149.pattern420 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0149.pattern420) descriptor420 checked420 (hRep descriptor420.representative)

def descriptor421 : OrbitDescriptor := ⟨30, 21, true⟩

theorem checked421 : orbitPatternTransform descriptor421 (Generated.Chunk0149.pattern421) =
    orbitRepresentativePattern descriptor421.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf421 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0149.pattern421 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0149.pattern421) descriptor421 checked421 (hRep descriptor421.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0149.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0149.regionContext := by
  apply Generated.FunctionalChunk0149.valid
  · exact leaf417 hRep
  · exact leaf418 hRep
  · exact leaf419 hRep
  · exact leaf420 hRep
  · exact leaf421 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0149

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0150
def descriptor422 : OrbitDescriptor := ⟨36, 4, false⟩

theorem checked422 : orbitPatternTransform descriptor422 (Generated.Chunk0150.pattern422) =
    orbitRepresentativePattern descriptor422.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf422 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0150.pattern422 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0150.pattern422) descriptor422 checked422 (hRep descriptor422.representative)

def descriptor423 : OrbitDescriptor := ⟨37, 4, false⟩

theorem checked423 : orbitPatternTransform descriptor423 (Generated.Chunk0150.pattern423) =
    orbitRepresentativePattern descriptor423.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf423 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0150.pattern423 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0150.pattern423) descriptor423 checked423 (hRep descriptor423.representative)

def descriptor424 : OrbitDescriptor := ⟨38, 4, false⟩

theorem checked424 : orbitPatternTransform descriptor424 (Generated.Chunk0150.pattern424) =
    orbitRepresentativePattern descriptor424.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf424 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0150.pattern424 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0150.pattern424) descriptor424 checked424 (hRep descriptor424.representative)

def descriptor425 : OrbitDescriptor := ⟨42, 4, false⟩

theorem checked425 : orbitPatternTransform descriptor425 (Generated.Chunk0150.pattern425) =
    orbitRepresentativePattern descriptor425.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf425 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0150.pattern425 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0150.pattern425) descriptor425 checked425 (hRep descriptor425.representative)

def descriptor426 : OrbitDescriptor := ⟨45, 4, false⟩

theorem checked426 : orbitPatternTransform descriptor426 (Generated.Chunk0150.pattern426) =
    orbitRepresentativePattern descriptor426.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf426 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0150.pattern426 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0150.pattern426) descriptor426 checked426 (hRep descriptor426.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0150.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0150.regionContext := by
  apply Generated.FunctionalChunk0150.valid
  · exact leaf422 hRep
  · exact leaf423 hRep
  · exact leaf424 hRep
  · exact leaf425 hRep
  · exact leaf426 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0150

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0151
def descriptor427 : OrbitDescriptor := ⟨42, 5, false⟩

theorem checked427 : orbitPatternTransform descriptor427 (Generated.Chunk0151.pattern427) =
    orbitRepresentativePattern descriptor427.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf427 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0151.pattern427 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0151.pattern427) descriptor427 checked427 (hRep descriptor427.representative)

def descriptor428 : OrbitDescriptor := ⟨55, 4, false⟩

theorem checked428 : orbitPatternTransform descriptor428 (Generated.Chunk0151.pattern428) =
    orbitRepresentativePattern descriptor428.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf428 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0151.pattern428 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0151.pattern428) descriptor428 checked428 (hRep descriptor428.representative)

def descriptor429 : OrbitDescriptor := ⟨58, 4, false⟩

theorem checked429 : orbitPatternTransform descriptor429 (Generated.Chunk0151.pattern429) =
    orbitRepresentativePattern descriptor429.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf429 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0151.pattern429 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0151.pattern429) descriptor429 checked429 (hRep descriptor429.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0151.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0151.regionContext := by
  apply Generated.FunctionalChunk0151.valid
  · exact leaf427 hRep
  · exact leaf428 hRep
  · exact leaf429 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0151
