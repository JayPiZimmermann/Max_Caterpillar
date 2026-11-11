import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0184
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0185
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0186
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0187
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0188
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0189
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0190
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0191
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0184
def descriptor520 : OrbitDescriptor := ⟨47, 15, true⟩

theorem checked520 : orbitPatternTransform descriptor520 (Generated.Chunk0184.pattern520) =
    orbitRepresentativePattern descriptor520.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf520 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0184.pattern520 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0184.pattern520) descriptor520 checked520 (hRep descriptor520.representative)

def descriptor521 : OrbitDescriptor := ⟨46, 15, true⟩

theorem checked521 : orbitPatternTransform descriptor521 (Generated.Chunk0184.pattern521) =
    orbitRepresentativePattern descriptor521.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf521 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0184.pattern521 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0184.pattern521) descriptor521 checked521 (hRep descriptor521.representative)

def descriptor522 : OrbitDescriptor := ⟨45, 15, true⟩

theorem checked522 : orbitPatternTransform descriptor522 (Generated.Chunk0184.pattern522) =
    orbitRepresentativePattern descriptor522.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf522 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0184.pattern522 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0184.pattern522) descriptor522 checked522 (hRep descriptor522.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0184.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0184.regionContext := by
  apply Generated.FunctionalChunk0184.valid
  · exact leaf520 hRep
  · exact leaf521 hRep
  · exact leaf522 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0184

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0185
def descriptor523 : OrbitDescriptor := ⟨30, 15, true⟩

theorem checked523 : orbitPatternTransform descriptor523 (Generated.Chunk0185.pattern523) =
    orbitRepresentativePattern descriptor523.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf523 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0185.pattern523 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0185.pattern523) descriptor523 checked523 (hRep descriptor523.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0185.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0185.regionContext := by
  apply Generated.FunctionalChunk0185.valid
  · exact leaf523 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0185

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0186
def descriptor524 : OrbitDescriptor := ⟨9, 15, true⟩

theorem checked524 : orbitPatternTransform descriptor524 (Generated.Chunk0186.pattern524) =
    orbitRepresentativePattern descriptor524.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf524 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0186.pattern524 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0186.pattern524) descriptor524 checked524 (hRep descriptor524.representative)

def descriptor525 : OrbitDescriptor := ⟨8, 15, true⟩

theorem checked525 : orbitPatternTransform descriptor525 (Generated.Chunk0186.pattern525) =
    orbitRepresentativePattern descriptor525.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf525 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0186.pattern525 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0186.pattern525) descriptor525 checked525 (hRep descriptor525.representative)

def descriptor526 : OrbitDescriptor := ⟨7, 15, true⟩

theorem checked526 : orbitPatternTransform descriptor526 (Generated.Chunk0186.pattern526) =
    orbitRepresentativePattern descriptor526.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf526 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0186.pattern526 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0186.pattern526) descriptor526 checked526 (hRep descriptor526.representative)

def descriptor527 : OrbitDescriptor := ⟨6, 17, true⟩

theorem checked527 : orbitPatternTransform descriptor527 (Generated.Chunk0186.pattern527) =
    orbitRepresentativePattern descriptor527.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf527 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0186.pattern527 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0186.pattern527) descriptor527 checked527 (hRep descriptor527.representative)

def descriptor528 : OrbitDescriptor := ⟨4, 17, true⟩

theorem checked528 : orbitPatternTransform descriptor528 (Generated.Chunk0186.pattern528) =
    orbitRepresentativePattern descriptor528.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf528 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0186.pattern528 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0186.pattern528) descriptor528 checked528 (hRep descriptor528.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0186.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0186.regionContext := by
  apply Generated.FunctionalChunk0186.valid
  · exact leaf524 hRep
  · exact leaf525 hRep
  · exact leaf526 hRep
  · exact leaf527 hRep
  · exact leaf528 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0186

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0187
def descriptor529 : OrbitDescriptor := ⟨3, 16, false⟩

theorem checked529 : orbitPatternTransform descriptor529 (Generated.Chunk0187.pattern529) =
    orbitRepresentativePattern descriptor529.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf529 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0187.pattern529 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0187.pattern529) descriptor529 checked529 (hRep descriptor529.representative)

def descriptor530 : OrbitDescriptor := ⟨5, 13, false⟩

theorem checked530 : orbitPatternTransform descriptor530 (Generated.Chunk0187.pattern530) =
    orbitRepresentativePattern descriptor530.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf530 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0187.pattern530 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0187.pattern530) descriptor530 checked530 (hRep descriptor530.representative)

def descriptor531 : OrbitDescriptor := ⟨6, 13, false⟩

theorem checked531 : orbitPatternTransform descriptor531 (Generated.Chunk0187.pattern531) =
    orbitRepresentativePattern descriptor531.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf531 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0187.pattern531 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0187.pattern531) descriptor531 checked531 (hRep descriptor531.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0187.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0187.regionContext := by
  apply Generated.FunctionalChunk0187.valid
  · exact leaf529 hRep
  · exact leaf530 hRep
  · exact leaf531 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0187

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0188
def descriptor532 : OrbitDescriptor := ⟨29, 13, false⟩

theorem checked532 : orbitPatternTransform descriptor532 (Generated.Chunk0188.pattern532) =
    orbitRepresentativePattern descriptor532.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf532 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0188.pattern532 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0188.pattern532) descriptor532 checked532 (hRep descriptor532.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0188.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0188.regionContext := by
  apply Generated.FunctionalChunk0188.valid
  · exact leaf532 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0188

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0189
def descriptor533 : OrbitDescriptor := ⟨42, 13, false⟩

theorem checked533 : orbitPatternTransform descriptor533 (Generated.Chunk0189.pattern533) =
    orbitRepresentativePattern descriptor533.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf533 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0189.pattern533 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0189.pattern533) descriptor533 checked533 (hRep descriptor533.representative)

def descriptor534 : OrbitDescriptor := ⟨43, 13, false⟩

theorem checked534 : orbitPatternTransform descriptor534 (Generated.Chunk0189.pattern534) =
    orbitRepresentativePattern descriptor534.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf534 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0189.pattern534 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0189.pattern534) descriptor534 checked534 (hRep descriptor534.representative)

def descriptor535 : OrbitDescriptor := ⟨44, 13, false⟩

theorem checked535 : orbitPatternTransform descriptor535 (Generated.Chunk0189.pattern535) =
    orbitRepresentativePattern descriptor535.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf535 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0189.pattern535 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0189.pattern535) descriptor535 checked535 (hRep descriptor535.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0189.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0189.regionContext := by
  apply Generated.FunctionalChunk0189.valid
  · exact leaf533 hRep
  · exact leaf534 hRep
  · exact leaf535 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0189

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0190
def descriptor536 : OrbitDescriptor := ⟨55, 12, false⟩

theorem checked536 : orbitPatternTransform descriptor536 (Generated.Chunk0190.pattern536) =
    orbitRepresentativePattern descriptor536.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf536 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0190.pattern536 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0190.pattern536) descriptor536 checked536 (hRep descriptor536.representative)

def descriptor537 : OrbitDescriptor := ⟨56, 12, false⟩

theorem checked537 : orbitPatternTransform descriptor537 (Generated.Chunk0190.pattern537) =
    orbitRepresentativePattern descriptor537.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf537 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0190.pattern537 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0190.pattern537) descriptor537 checked537 (hRep descriptor537.representative)

def descriptor538 : OrbitDescriptor := ⟨57, 12, false⟩

theorem checked538 : orbitPatternTransform descriptor538 (Generated.Chunk0190.pattern538) =
    orbitRepresentativePattern descriptor538.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf538 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0190.pattern538 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0190.pattern538) descriptor538 checked538 (hRep descriptor538.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0190.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0190.regionContext := by
  apply Generated.FunctionalChunk0190.valid
  · exact leaf536 hRep
  · exact leaf537 hRep
  · exact leaf538 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0190

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0191
def descriptor539 : OrbitDescriptor := ⟨58, 12, false⟩

theorem checked539 : orbitPatternTransform descriptor539 (Generated.Chunk0191.pattern539) =
    orbitRepresentativePattern descriptor539.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf539 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern539 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern539) descriptor539 checked539 (hRep descriptor539.representative)

def descriptor540 : OrbitDescriptor := ⟨59, 12, false⟩

theorem checked540 : orbitPatternTransform descriptor540 (Generated.Chunk0191.pattern540) =
    orbitRepresentativePattern descriptor540.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf540 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern540 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern540) descriptor540 checked540 (hRep descriptor540.representative)

def descriptor541 : OrbitDescriptor := ⟨60, 12, false⟩

theorem checked541 : orbitPatternTransform descriptor541 (Generated.Chunk0191.pattern541) =
    orbitRepresentativePattern descriptor541.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf541 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern541 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern541) descriptor541 checked541 (hRep descriptor541.representative)

def descriptor542 : OrbitDescriptor := ⟨61, 12, false⟩

theorem checked542 : orbitPatternTransform descriptor542 (Generated.Chunk0191.pattern542) =
    orbitRepresentativePattern descriptor542.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf542 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern542 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern542) descriptor542 checked542 (hRep descriptor542.representative)

def descriptor543 : OrbitDescriptor := ⟨60, 20, true⟩

theorem checked543 : orbitPatternTransform descriptor543 (Generated.Chunk0191.pattern543) =
    orbitRepresentativePattern descriptor543.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf543 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern543 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern543) descriptor543 checked543 (hRep descriptor543.representative)

def descriptor544 : OrbitDescriptor := ⟨59, 20, true⟩

theorem checked544 : orbitPatternTransform descriptor544 (Generated.Chunk0191.pattern544) =
    orbitRepresentativePattern descriptor544.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf544 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern544 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern544) descriptor544 checked544 (hRep descriptor544.representative)

def descriptor545 : OrbitDescriptor := ⟨58, 20, true⟩

theorem checked545 : orbitPatternTransform descriptor545 (Generated.Chunk0191.pattern545) =
    orbitRepresentativePattern descriptor545.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf545 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0191.pattern545 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0191.pattern545) descriptor545 checked545 (hRep descriptor545.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0191.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0191.regionContext := by
  apply Generated.FunctionalChunk0191.valid
  · exact leaf539 hRep
  · exact leaf540 hRep
  · exact leaf541 hRep
  · exact leaf542 hRep
  · exact leaf543 hRep
  · exact leaf544 hRep
  · exact leaf545 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0191
