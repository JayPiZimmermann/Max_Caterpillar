import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0016
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0017
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0018
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0019
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0020
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0021
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0022
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0023
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0016
def descriptor46 : OrbitDescriptor := ⟨13, 12, false⟩

theorem checked46 : orbitPatternTransform descriptor46 (Generated.Chunk0016.pattern46) =
    orbitRepresentativePattern descriptor46.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf46 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0016.pattern46 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0016.pattern46) descriptor46 checked46 (hRep descriptor46.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0016.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0016.regionContext := by
  apply Generated.FunctionalChunk0016.valid
  · exact leaf46 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0016

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0017
def descriptor47 : OrbitDescriptor := ⟨16, 12, false⟩

theorem checked47 : orbitPatternTransform descriptor47 (Generated.Chunk0017.pattern47) =
    orbitRepresentativePattern descriptor47.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf47 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0017.pattern47 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0017.pattern47) descriptor47 checked47 (hRep descriptor47.representative)

def descriptor48 : OrbitDescriptor := ⟨18, 2, false⟩

theorem checked48 : orbitPatternTransform descriptor48 (Generated.Chunk0017.pattern48) =
    orbitRepresentativePattern descriptor48.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf48 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0017.pattern48 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0017.pattern48) descriptor48 checked48 (hRep descriptor48.representative)

def descriptor49 : OrbitDescriptor := ⟨19, 2, false⟩

theorem checked49 : orbitPatternTransform descriptor49 (Generated.Chunk0017.pattern49) =
    orbitRepresentativePattern descriptor49.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf49 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0017.pattern49 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0017.pattern49) descriptor49 checked49 (hRep descriptor49.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0017.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0017.regionContext := by
  apply Generated.FunctionalChunk0017.valid
  · exact leaf47 hRep
  · exact leaf48 hRep
  · exact leaf49 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0017

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0018
def descriptor50 : OrbitDescriptor := ⟨18, 8, false⟩

theorem checked50 : orbitPatternTransform descriptor50 (Generated.Chunk0018.pattern50) =
    orbitRepresentativePattern descriptor50.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf50 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0018.pattern50 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0018.pattern50) descriptor50 checked50 (hRep descriptor50.representative)

def descriptor51 : OrbitDescriptor := ⟨21, 0, false⟩

theorem checked51 : orbitPatternTransform descriptor51 (Generated.Chunk0018.pattern51) =
    orbitRepresentativePattern descriptor51.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf51 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0018.pattern51 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0018.pattern51) descriptor51 checked51 (hRep descriptor51.representative)

def descriptor52 : OrbitDescriptor := ⟨22, 0, false⟩

theorem checked52 : orbitPatternTransform descriptor52 (Generated.Chunk0018.pattern52) =
    orbitRepresentativePattern descriptor52.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf52 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0018.pattern52 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0018.pattern52) descriptor52 checked52 (hRep descriptor52.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0018.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0018.regionContext := by
  apply Generated.FunctionalChunk0018.valid
  · exact leaf50 hRep
  · exact leaf51 hRep
  · exact leaf52 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0018

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0019
def descriptor53 : OrbitDescriptor := ⟨19, 8, false⟩

theorem checked53 : orbitPatternTransform descriptor53 (Generated.Chunk0019.pattern53) =
    orbitRepresentativePattern descriptor53.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf53 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0019.pattern53 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0019.pattern53) descriptor53 checked53 (hRep descriptor53.representative)

def descriptor54 : OrbitDescriptor := ⟨22, 6, false⟩

theorem checked54 : orbitPatternTransform descriptor54 (Generated.Chunk0019.pattern54) =
    orbitRepresentativePattern descriptor54.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf54 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0019.pattern54 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0019.pattern54) descriptor54 checked54 (hRep descriptor54.representative)

def descriptor55 : OrbitDescriptor := ⟨23, 0, false⟩

theorem checked55 : orbitPatternTransform descriptor55 (Generated.Chunk0019.pattern55) =
    orbitRepresentativePattern descriptor55.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf55 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0019.pattern55 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0019.pattern55) descriptor55 checked55 (hRep descriptor55.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0019.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0019.regionContext := by
  apply Generated.FunctionalChunk0019.valid
  · exact leaf53 hRep
  · exact leaf54 hRep
  · exact leaf55 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0019

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0020
def descriptor56 : OrbitDescriptor := ⟨9, 12, false⟩

theorem checked56 : orbitPatternTransform descriptor56 (Generated.Chunk0020.pattern56) =
    orbitRepresentativePattern descriptor56.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf56 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0020.pattern56 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0020.pattern56) descriptor56 checked56 (hRep descriptor56.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0020.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0020.regionContext := by
  apply Generated.FunctionalChunk0020.valid
  · exact leaf56 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0020

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0021
def descriptor57 : OrbitDescriptor := ⟨14, 12, false⟩

theorem checked57 : orbitPatternTransform descriptor57 (Generated.Chunk0021.pattern57) =
    orbitRepresentativePattern descriptor57.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf57 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0021.pattern57 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0021.pattern57) descriptor57 checked57 (hRep descriptor57.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0021.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0021.regionContext := by
  apply Generated.FunctionalChunk0021.valid
  · exact leaf57 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0021

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0022
def descriptor58 : OrbitDescriptor := ⟨17, 12, false⟩

theorem checked58 : orbitPatternTransform descriptor58 (Generated.Chunk0022.pattern58) =
    orbitRepresentativePattern descriptor58.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf58 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0022.pattern58 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0022.pattern58) descriptor58 checked58 (hRep descriptor58.representative)

def descriptor59 : OrbitDescriptor := ⟨19, 12, false⟩

theorem checked59 : orbitPatternTransform descriptor59 (Generated.Chunk0022.pattern59) =
    orbitRepresentativePattern descriptor59.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf59 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0022.pattern59 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0022.pattern59) descriptor59 checked59 (hRep descriptor59.representative)

def descriptor60 : OrbitDescriptor := ⟨20, 2, false⟩

theorem checked60 : orbitPatternTransform descriptor60 (Generated.Chunk0022.pattern60) =
    orbitRepresentativePattern descriptor60.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf60 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0022.pattern60 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0022.pattern60) descriptor60 checked60 (hRep descriptor60.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0022.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0022.regionContext := by
  apply Generated.FunctionalChunk0022.valid
  · exact leaf58 hRep
  · exact leaf59 hRep
  · exact leaf60 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0022

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0023
def descriptor61 : OrbitDescriptor := ⟨19, 14, false⟩

theorem checked61 : orbitPatternTransform descriptor61 (Generated.Chunk0023.pattern61) =
    orbitRepresentativePattern descriptor61.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf61 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0023.pattern61 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0023.pattern61) descriptor61 checked61 (hRep descriptor61.representative)

def descriptor62 : OrbitDescriptor := ⟨22, 12, false⟩

theorem checked62 : orbitPatternTransform descriptor62 (Generated.Chunk0023.pattern62) =
    orbitRepresentativePattern descriptor62.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf62 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0023.pattern62 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0023.pattern62) descriptor62 checked62 (hRep descriptor62.representative)

def descriptor63 : OrbitDescriptor := ⟨23, 2, false⟩

theorem checked63 : orbitPatternTransform descriptor63 (Generated.Chunk0023.pattern63) =
    orbitRepresentativePattern descriptor63.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf63 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0023.pattern63 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0023.pattern63) descriptor63 checked63 (hRep descriptor63.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0023.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0023.regionContext := by
  apply Generated.FunctionalChunk0023.valid
  · exact leaf61 hRep
  · exact leaf62 hRep
  · exact leaf63 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0023
