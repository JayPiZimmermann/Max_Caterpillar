import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0168
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0169
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0170
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0171
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0172
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0173
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0174
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0175
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0168
def descriptor470 : OrbitDescriptor := ⟨38, 18, false⟩

theorem checked470 : orbitPatternTransform descriptor470 (Generated.Chunk0168.pattern470) =
    orbitRepresentativePattern descriptor470.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf470 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0168.pattern470 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0168.pattern470) descriptor470 checked470 (hRep descriptor470.representative)

def descriptor471 : OrbitDescriptor := ⟨40, 18, false⟩

theorem checked471 : orbitPatternTransform descriptor471 (Generated.Chunk0168.pattern471) =
    orbitRepresentativePattern descriptor471.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf471 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0168.pattern471 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0168.pattern471) descriptor471 checked471 (hRep descriptor471.representative)

def descriptor472 : OrbitDescriptor := ⟨41, 4, false⟩

theorem checked472 : orbitPatternTransform descriptor472 (Generated.Chunk0168.pattern472) =
    orbitRepresentativePattern descriptor472.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf472 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0168.pattern472 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0168.pattern472) descriptor472 checked472 (hRep descriptor472.representative)

def descriptor473 : OrbitDescriptor := ⟨44, 4, false⟩

theorem checked473 : orbitPatternTransform descriptor473 (Generated.Chunk0168.pattern473) =
    orbitRepresentativePattern descriptor473.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf473 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0168.pattern473 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0168.pattern473) descriptor473 checked473 (hRep descriptor473.representative)

def descriptor474 : OrbitDescriptor := ⟨47, 4, false⟩

theorem checked474 : orbitPatternTransform descriptor474 (Generated.Chunk0168.pattern474) =
    orbitRepresentativePattern descriptor474.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf474 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0168.pattern474 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0168.pattern474) descriptor474 checked474 (hRep descriptor474.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0168.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0168.regionContext := by
  apply Generated.FunctionalChunk0168.valid
  · exact leaf470 hRep
  · exact leaf471 hRep
  · exact leaf472 hRep
  · exact leaf473 hRep
  · exact leaf474 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0168

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0169
def descriptor475 : OrbitDescriptor := ⟨44, 5, false⟩

theorem checked475 : orbitPatternTransform descriptor475 (Generated.Chunk0169.pattern475) =
    orbitRepresentativePattern descriptor475.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf475 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0169.pattern475 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0169.pattern475) descriptor475 checked475 (hRep descriptor475.representative)

def descriptor476 : OrbitDescriptor := ⟨57, 4, false⟩

theorem checked476 : orbitPatternTransform descriptor476 (Generated.Chunk0169.pattern476) =
    orbitRepresentativePattern descriptor476.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf476 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0169.pattern476 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0169.pattern476) descriptor476 checked476 (hRep descriptor476.representative)

def descriptor477 : OrbitDescriptor := ⟨60, 4, false⟩

theorem checked477 : orbitPatternTransform descriptor477 (Generated.Chunk0169.pattern477) =
    orbitRepresentativePattern descriptor477.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf477 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0169.pattern477 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0169.pattern477) descriptor477 checked477 (hRep descriptor477.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0169.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0169.regionContext := by
  apply Generated.FunctionalChunk0169.valid
  · exact leaf475 hRep
  · exact leaf476 hRep
  · exact leaf477 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0169

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0170
def descriptor478 : OrbitDescriptor := ⟨47, 5, false⟩

theorem checked478 : orbitPatternTransform descriptor478 (Generated.Chunk0170.pattern478) =
    orbitRepresentativePattern descriptor478.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf478 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0170.pattern478 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0170.pattern478) descriptor478 checked478 (hRep descriptor478.representative)

def descriptor479 : OrbitDescriptor := ⟨60, 5, false⟩

theorem checked479 : orbitPatternTransform descriptor479 (Generated.Chunk0170.pattern479) =
    orbitRepresentativePattern descriptor479.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf479 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0170.pattern479 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0170.pattern479) descriptor479 checked479 (hRep descriptor479.representative)

def descriptor480 : OrbitDescriptor := ⟨52, 9, true⟩

theorem checked480 : orbitPatternTransform descriptor480 (Generated.Chunk0170.pattern480) =
    orbitRepresentativePattern descriptor480.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf480 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0170.pattern480 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0170.pattern480) descriptor480 checked480 (hRep descriptor480.representative)

def descriptor481 : OrbitDescriptor := ⟨51, 9, true⟩

theorem checked481 : orbitPatternTransform descriptor481 (Generated.Chunk0170.pattern481) =
    orbitRepresentativePattern descriptor481.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf481 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0170.pattern481 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0170.pattern481) descriptor481 checked481 (hRep descriptor481.representative)

def descriptor482 : OrbitDescriptor := ⟨50, 9, true⟩

theorem checked482 : orbitPatternTransform descriptor482 (Generated.Chunk0170.pattern482) =
    orbitRepresentativePattern descriptor482.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf482 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0170.pattern482 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0170.pattern482) descriptor482 checked482 (hRep descriptor482.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0170.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0170.regionContext := by
  apply Generated.FunctionalChunk0170.valid
  · exact leaf478 hRep
  · exact leaf479 hRep
  · exact leaf480 hRep
  · exact leaf481 hRep
  · exact leaf482 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0170

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0171
def descriptor483 : OrbitDescriptor := ⟨33, 9, true⟩

theorem checked483 : orbitPatternTransform descriptor483 (Generated.Chunk0171.pattern483) =
    orbitRepresentativePattern descriptor483.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf483 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0171.pattern483 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0171.pattern483) descriptor483 checked483 (hRep descriptor483.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0171.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0171.regionContext := by
  apply Generated.FunctionalChunk0171.valid
  · exact leaf483 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0171

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0172
def descriptor484 : OrbitDescriptor := ⟨20, 9, true⟩

theorem checked484 : orbitPatternTransform descriptor484 (Generated.Chunk0172.pattern484) =
    orbitRepresentativePattern descriptor484.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf484 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0172.pattern484 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0172.pattern484) descriptor484 checked484 (hRep descriptor484.representative)

def descriptor485 : OrbitDescriptor := ⟨19, 15, true⟩

theorem checked485 : orbitPatternTransform descriptor485 (Generated.Chunk0172.pattern485) =
    orbitRepresentativePattern descriptor485.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf485 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0172.pattern485 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0172.pattern485) descriptor485 checked485 (hRep descriptor485.representative)

def descriptor486 : OrbitDescriptor := ⟨17, 15, true⟩

theorem checked486 : orbitPatternTransform descriptor486 (Generated.Chunk0172.pattern486) =
    orbitRepresentativePattern descriptor486.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf486 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0172.pattern486 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0172.pattern486) descriptor486 checked486 (hRep descriptor486.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0172.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0172.regionContext := by
  apply Generated.FunctionalChunk0172.valid
  · exact leaf484 hRep
  · exact leaf485 hRep
  · exact leaf486 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0172

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0173
def descriptor487 : OrbitDescriptor := ⟨19, 9, true⟩

theorem checked487 : orbitPatternTransform descriptor487 (Generated.Chunk0173.pattern487) =
    orbitRepresentativePattern descriptor487.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf487 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0173.pattern487 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0173.pattern487) descriptor487 checked487 (hRep descriptor487.representative)

def descriptor488 : OrbitDescriptor := ⟨18, 9, true⟩

theorem checked488 : orbitPatternTransform descriptor488 (Generated.Chunk0173.pattern488) =
    orbitRepresentativePattern descriptor488.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf488 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0173.pattern488 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0173.pattern488) descriptor488 checked488 (hRep descriptor488.representative)

def descriptor489 : OrbitDescriptor := ⟨16, 15, true⟩

theorem checked489 : orbitPatternTransform descriptor489 (Generated.Chunk0173.pattern489) =
    orbitRepresentativePattern descriptor489.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf489 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0173.pattern489 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0173.pattern489) descriptor489 checked489 (hRep descriptor489.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0173.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0173.regionContext := by
  apply Generated.FunctionalChunk0173.valid
  · exact leaf487 hRep
  · exact leaf488 hRep
  · exact leaf489 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0173

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0174
def descriptor490 : OrbitDescriptor := ⟨17, 9, true⟩

theorem checked490 : orbitPatternTransform descriptor490 (Generated.Chunk0174.pattern490) =
    orbitRepresentativePattern descriptor490.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf490 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0174.pattern490 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0174.pattern490) descriptor490 checked490 (hRep descriptor490.representative)

def descriptor491 : OrbitDescriptor := ⟨16, 9, true⟩

theorem checked491 : orbitPatternTransform descriptor491 (Generated.Chunk0174.pattern491) =
    orbitRepresentativePattern descriptor491.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf491 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0174.pattern491 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0174.pattern491) descriptor491 checked491 (hRep descriptor491.representative)

def descriptor492 : OrbitDescriptor := ⟨15, 9, true⟩

theorem checked492 : orbitPatternTransform descriptor492 (Generated.Chunk0174.pattern492) =
    orbitRepresentativePattern descriptor492.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf492 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0174.pattern492 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0174.pattern492) descriptor492 checked492 (hRep descriptor492.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0174.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0174.regionContext := by
  apply Generated.FunctionalChunk0174.valid
  · exact leaf490 hRep
  · exact leaf491 hRep
  · exact leaf492 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0174

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0175
def descriptor493 : OrbitDescriptor := ⟨12, 21, true⟩

theorem checked493 : orbitPatternTransform descriptor493 (Generated.Chunk0175.pattern493) =
    orbitRepresentativePattern descriptor493.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf493 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0175.pattern493 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0175.pattern493) descriptor493 checked493 (hRep descriptor493.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0175.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0175.regionContext := by
  apply Generated.FunctionalChunk0175.valid
  · exact leaf493 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0175
