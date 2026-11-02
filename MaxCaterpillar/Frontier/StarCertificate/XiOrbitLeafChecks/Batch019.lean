import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0152
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0153
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0154
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0155
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0156
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0157
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0158
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0159
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0152
def descriptor430 : OrbitDescriptor := ⟨45, 5, false⟩

theorem checked430 : orbitPatternTransform descriptor430 (Generated.Chunk0152.pattern430) =
    orbitRepresentativePattern descriptor430.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf430 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0152.pattern430 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0152.pattern430) descriptor430 checked430 (hRep descriptor430.representative)

def descriptor431 : OrbitDescriptor := ⟨58, 5, false⟩

theorem checked431 : orbitPatternTransform descriptor431 (Generated.Chunk0152.pattern431) =
    orbitRepresentativePattern descriptor431.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf431 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0152.pattern431 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0152.pattern431) descriptor431 checked431 (hRep descriptor431.representative)

def descriptor432 : OrbitDescriptor := ⟨54, 9, true⟩

theorem checked432 : orbitPatternTransform descriptor432 (Generated.Chunk0152.pattern432) =
    orbitRepresentativePattern descriptor432.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf432 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0152.pattern432 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0152.pattern432) descriptor432 checked432 (hRep descriptor432.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0152.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0152.regionContext := by
  apply Generated.FunctionalChunk0152.valid
  · exact leaf430 hRep
  · exact leaf431 hRep
  · exact leaf432 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0152

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0153
def descriptor433 : OrbitDescriptor := ⟨35, 9, true⟩

theorem checked433 : orbitPatternTransform descriptor433 (Generated.Chunk0153.pattern433) =
    orbitRepresentativePattern descriptor433.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf433 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0153.pattern433 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0153.pattern433) descriptor433 checked433 (hRep descriptor433.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0153.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0153.regionContext := by
  apply Generated.FunctionalChunk0153.valid
  · exact leaf433 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0153

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0154
def descriptor434 : OrbitDescriptor := ⟨26, 9, true⟩

theorem checked434 : orbitPatternTransform descriptor434 (Generated.Chunk0154.pattern434) =
    orbitRepresentativePattern descriptor434.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf434 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0154.pattern434 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0154.pattern434) descriptor434 checked434 (hRep descriptor434.representative)

def descriptor435 : OrbitDescriptor := ⟨25, 9, true⟩

theorem checked435 : orbitPatternTransform descriptor435 (Generated.Chunk0154.pattern435) =
    orbitRepresentativePattern descriptor435.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf435 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0154.pattern435 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0154.pattern435) descriptor435 checked435 (hRep descriptor435.representative)

def descriptor436 : OrbitDescriptor := ⟨24, 9, true⟩

theorem checked436 : orbitPatternTransform descriptor436 (Generated.Chunk0154.pattern436) =
    orbitRepresentativePattern descriptor436.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf436 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0154.pattern436 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0154.pattern436) descriptor436 checked436 (hRep descriptor436.representative)

def descriptor437 : OrbitDescriptor := ⟨23, 17, true⟩

theorem checked437 : orbitPatternTransform descriptor437 (Generated.Chunk0154.pattern437) =
    orbitRepresentativePattern descriptor437.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf437 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0154.pattern437 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0154.pattern437) descriptor437 checked437 (hRep descriptor437.representative)

def descriptor438 : OrbitDescriptor := ⟨20, 17, true⟩

theorem checked438 : orbitPatternTransform descriptor438 (Generated.Chunk0154.pattern438) =
    orbitRepresentativePattern descriptor438.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf438 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0154.pattern438 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0154.pattern438) descriptor438 checked438 (hRep descriptor438.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0154.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0154.regionContext := by
  apply Generated.FunctionalChunk0154.valid
  · exact leaf434 hRep
  · exact leaf435 hRep
  · exact leaf436 hRep
  · exact leaf437 hRep
  · exact leaf438 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0154

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0155
def descriptor439 : OrbitDescriptor := ⟨23, 11, true⟩

theorem checked439 : orbitPatternTransform descriptor439 (Generated.Chunk0155.pattern439) =
    orbitRepresentativePattern descriptor439.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf439 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0155.pattern439 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0155.pattern439) descriptor439 checked439 (hRep descriptor439.representative)

def descriptor440 : OrbitDescriptor := ⟨22, 21, true⟩

theorem checked440 : orbitPatternTransform descriptor440 (Generated.Chunk0155.pattern440) =
    orbitRepresentativePattern descriptor440.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf440 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0155.pattern440 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0155.pattern440) descriptor440 checked440 (hRep descriptor440.representative)

def descriptor441 : OrbitDescriptor := ⟨19, 23, true⟩

theorem checked441 : orbitPatternTransform descriptor441 (Generated.Chunk0155.pattern441) =
    orbitRepresentativePattern descriptor441.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf441 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0155.pattern441 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0155.pattern441) descriptor441 checked441 (hRep descriptor441.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0155.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0155.regionContext := by
  apply Generated.FunctionalChunk0155.valid
  · exact leaf439 hRep
  · exact leaf440 hRep
  · exact leaf441 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0155

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0156
def descriptor442 : OrbitDescriptor := ⟨20, 11, true⟩

theorem checked442 : orbitPatternTransform descriptor442 (Generated.Chunk0156.pattern442) =
    orbitRepresentativePattern descriptor442.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf442 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0156.pattern442 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0156.pattern442) descriptor442 checked442 (hRep descriptor442.representative)

def descriptor443 : OrbitDescriptor := ⟨19, 21, true⟩

theorem checked443 : orbitPatternTransform descriptor443 (Generated.Chunk0156.pattern443) =
    orbitRepresentativePattern descriptor443.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf443 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0156.pattern443 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0156.pattern443) descriptor443 checked443 (hRep descriptor443.representative)

def descriptor444 : OrbitDescriptor := ⟨17, 21, true⟩

theorem checked444 : orbitPatternTransform descriptor444 (Generated.Chunk0156.pattern444) =
    orbitRepresentativePattern descriptor444.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf444 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0156.pattern444 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0156.pattern444) descriptor444 checked444 (hRep descriptor444.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0156.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0156.regionContext := by
  apply Generated.FunctionalChunk0156.valid
  · exact leaf442 hRep
  · exact leaf443 hRep
  · exact leaf444 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0156

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0157
def descriptor445 : OrbitDescriptor := ⟨14, 21, true⟩

theorem checked445 : orbitPatternTransform descriptor445 (Generated.Chunk0157.pattern445) =
    orbitRepresentativePattern descriptor445.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf445 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0157.pattern445 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0157.pattern445) descriptor445 checked445 (hRep descriptor445.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0157.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0157.regionContext := by
  apply Generated.FunctionalChunk0157.valid
  · exact leaf445 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0157

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0158
def descriptor446 : OrbitDescriptor := ⟨9, 21, true⟩

theorem checked446 : orbitPatternTransform descriptor446 (Generated.Chunk0158.pattern446) =
    orbitRepresentativePattern descriptor446.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf446 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0158.pattern446 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0158.pattern446) descriptor446 checked446 (hRep descriptor446.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0158.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0158.regionContext := by
  apply Generated.FunctionalChunk0158.valid
  · exact leaf446 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0158

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0159
def descriptor447 : OrbitDescriptor := ⟨37, 18, false⟩

theorem checked447 : orbitPatternTransform descriptor447 (Generated.Chunk0159.pattern447) =
    orbitRepresentativePattern descriptor447.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf447 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0159.pattern447 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0159.pattern447) descriptor447 checked447 (hRep descriptor447.representative)

def descriptor448 : OrbitDescriptor := ⟨39, 4, false⟩

theorem checked448 : orbitPatternTransform descriptor448 (Generated.Chunk0159.pattern448) =
    orbitRepresentativePattern descriptor448.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf448 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0159.pattern448 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0159.pattern448) descriptor448 checked448 (hRep descriptor448.representative)

def descriptor449 : OrbitDescriptor := ⟨40, 4, false⟩

theorem checked449 : orbitPatternTransform descriptor449 (Generated.Chunk0159.pattern449) =
    orbitRepresentativePattern descriptor449.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf449 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0159.pattern449 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0159.pattern449) descriptor449 checked449 (hRep descriptor449.representative)

def descriptor450 : OrbitDescriptor := ⟨43, 4, false⟩

theorem checked450 : orbitPatternTransform descriptor450 (Generated.Chunk0159.pattern450) =
    orbitRepresentativePattern descriptor450.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf450 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0159.pattern450 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0159.pattern450) descriptor450 checked450 (hRep descriptor450.representative)

def descriptor451 : OrbitDescriptor := ⟨46, 4, false⟩

theorem checked451 : orbitPatternTransform descriptor451 (Generated.Chunk0159.pattern451) =
    orbitRepresentativePattern descriptor451.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf451 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0159.pattern451 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0159.pattern451) descriptor451 checked451 (hRep descriptor451.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0159.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0159.regionContext := by
  apply Generated.FunctionalChunk0159.valid
  · exact leaf447 hRep
  · exact leaf448 hRep
  · exact leaf449 hRep
  · exact leaf450 hRep
  · exact leaf451 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0159
