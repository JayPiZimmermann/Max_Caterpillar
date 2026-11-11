import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0024
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0025
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0026
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0027
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0028
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0029
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0030
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0031
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0024
def descriptor64 : OrbitDescriptor := ⟨20, 8, false⟩

theorem checked64 : orbitPatternTransform descriptor64 (Generated.Chunk0024.pattern64) =
    orbitRepresentativePattern descriptor64.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf64 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0024.pattern64 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0024.pattern64) descriptor64 checked64 (hRep descriptor64.representative)

def descriptor65 : OrbitDescriptor := ⟨23, 8, false⟩

theorem checked65 : orbitPatternTransform descriptor65 (Generated.Chunk0024.pattern65) =
    orbitRepresentativePattern descriptor65.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf65 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0024.pattern65 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0024.pattern65) descriptor65 checked65 (hRep descriptor65.representative)

def descriptor66 : OrbitDescriptor := ⟨24, 0, false⟩

theorem checked66 : orbitPatternTransform descriptor66 (Generated.Chunk0024.pattern66) =
    orbitRepresentativePattern descriptor66.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf66 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0024.pattern66 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0024.pattern66) descriptor66 checked66 (hRep descriptor66.representative)

def descriptor67 : OrbitDescriptor := ⟨25, 0, false⟩

theorem checked67 : orbitPatternTransform descriptor67 (Generated.Chunk0024.pattern67) =
    orbitRepresentativePattern descriptor67.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf67 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0024.pattern67 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0024.pattern67) descriptor67 checked67 (hRep descriptor67.representative)

def descriptor68 : OrbitDescriptor := ⟨26, 0, false⟩

theorem checked68 : orbitPatternTransform descriptor68 (Generated.Chunk0024.pattern68) =
    orbitRepresentativePattern descriptor68.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf68 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0024.pattern68 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0024.pattern68) descriptor68 checked68 (hRep descriptor68.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0024.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0024.regionContext := by
  apply Generated.FunctionalChunk0024.valid
  · exact leaf64 hRep
  · exact leaf65 hRep
  · exact leaf66 hRep
  · exact leaf67 hRep
  · exact leaf68 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0024

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0025
def descriptor69 : OrbitDescriptor := ⟨1, 1, false⟩

theorem checked69 : orbitPatternTransform descriptor69 (Generated.Chunk0025.pattern69) =
    orbitRepresentativePattern descriptor69.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf69 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0025.pattern69 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0025.pattern69) descriptor69 checked69 (hRep descriptor69.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0025.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0025.regionContext := by
  apply Generated.FunctionalChunk0025.valid
  · exact leaf69 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0025

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0026
def descriptor70 : OrbitDescriptor := ⟨27, 0, false⟩

theorem checked70 : orbitPatternTransform descriptor70 (Generated.Chunk0026.pattern70) =
    orbitRepresentativePattern descriptor70.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf70 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0026.pattern70 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0026.pattern70) descriptor70 checked70 (hRep descriptor70.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0026.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0026.regionContext := by
  apply Generated.FunctionalChunk0026.valid
  · exact leaf70 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0026

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0027
def descriptor71 : OrbitDescriptor := ⟨28, 0, false⟩

theorem checked71 : orbitPatternTransform descriptor71 (Generated.Chunk0027.pattern71) =
    orbitRepresentativePattern descriptor71.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf71 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0027.pattern71 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0027.pattern71) descriptor71 checked71 (hRep descriptor71.representative)

def descriptor72 : OrbitDescriptor := ⟨29, 0, false⟩

theorem checked72 : orbitPatternTransform descriptor72 (Generated.Chunk0027.pattern72) =
    orbitRepresentativePattern descriptor72.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf72 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0027.pattern72 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0027.pattern72) descriptor72 checked72 (hRep descriptor72.representative)

def descriptor73 : OrbitDescriptor := ⟨30, 0, false⟩

theorem checked73 : orbitPatternTransform descriptor73 (Generated.Chunk0027.pattern73) =
    orbitRepresentativePattern descriptor73.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf73 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0027.pattern73 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0027.pattern73) descriptor73 checked73 (hRep descriptor73.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0027.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0027.regionContext := by
  apply Generated.FunctionalChunk0027.valid
  · exact leaf71 hRep
  · exact leaf72 hRep
  · exact leaf73 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0027

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0028
def descriptor74 : OrbitDescriptor := ⟨29, 6, false⟩

theorem checked74 : orbitPatternTransform descriptor74 (Generated.Chunk0028.pattern74) =
    orbitRepresentativePattern descriptor74.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf74 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0028.pattern74 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0028.pattern74) descriptor74 checked74 (hRep descriptor74.representative)

def descriptor75 : OrbitDescriptor := ⟨31, 0, false⟩

theorem checked75 : orbitPatternTransform descriptor75 (Generated.Chunk0028.pattern75) =
    orbitRepresentativePattern descriptor75.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf75 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0028.pattern75 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0028.pattern75) descriptor75 checked75 (hRep descriptor75.representative)

def descriptor76 : OrbitDescriptor := ⟨32, 0, false⟩

theorem checked76 : orbitPatternTransform descriptor76 (Generated.Chunk0028.pattern76) =
    orbitRepresentativePattern descriptor76.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf76 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0028.pattern76 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0028.pattern76) descriptor76 checked76 (hRep descriptor76.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0028.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0028.regionContext := by
  apply Generated.FunctionalChunk0028.valid
  · exact leaf74 hRep
  · exact leaf75 hRep
  · exact leaf76 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0028

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0029
def descriptor77 : OrbitDescriptor := ⟨30, 6, false⟩

theorem checked77 : orbitPatternTransform descriptor77 (Generated.Chunk0029.pattern77) =
    orbitRepresentativePattern descriptor77.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf77 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0029.pattern77 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0029.pattern77) descriptor77 checked77 (hRep descriptor77.representative)

def descriptor78 : OrbitDescriptor := ⟨32, 6, false⟩

theorem checked78 : orbitPatternTransform descriptor78 (Generated.Chunk0029.pattern78) =
    orbitRepresentativePattern descriptor78.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf78 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0029.pattern78 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0029.pattern78) descriptor78 checked78 (hRep descriptor78.representative)

def descriptor79 : OrbitDescriptor := ⟨33, 0, false⟩

theorem checked79 : orbitPatternTransform descriptor79 (Generated.Chunk0029.pattern79) =
    orbitRepresentativePattern descriptor79.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf79 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0029.pattern79 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0029.pattern79) descriptor79 checked79 (hRep descriptor79.representative)

def descriptor80 : OrbitDescriptor := ⟨34, 0, false⟩

theorem checked80 : orbitPatternTransform descriptor80 (Generated.Chunk0029.pattern80) =
    orbitRepresentativePattern descriptor80.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf80 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0029.pattern80 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0029.pattern80) descriptor80 checked80 (hRep descriptor80.representative)

def descriptor81 : OrbitDescriptor := ⟨35, 0, false⟩

theorem checked81 : orbitPatternTransform descriptor81 (Generated.Chunk0029.pattern81) =
    orbitRepresentativePattern descriptor81.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf81 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0029.pattern81 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0029.pattern81) descriptor81 checked81 (hRep descriptor81.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0029.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0029.regionContext := by
  apply Generated.FunctionalChunk0029.valid
  · exact leaf77 hRep
  · exact leaf78 hRep
  · exact leaf79 hRep
  · exact leaf80 hRep
  · exact leaf81 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0029

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0030
def descriptor82 : OrbitDescriptor := ⟨2, 1, false⟩

theorem checked82 : orbitPatternTransform descriptor82 (Generated.Chunk0030.pattern82) =
    orbitRepresentativePattern descriptor82.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf82 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0030.pattern82 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0030.pattern82) descriptor82 checked82 (hRep descriptor82.representative)

def descriptor83 : OrbitDescriptor := ⟨3, 1, false⟩

theorem checked83 : orbitPatternTransform descriptor83 (Generated.Chunk0030.pattern83) =
    orbitRepresentativePattern descriptor83.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf83 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0030.pattern83 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0030.pattern83) descriptor83 checked83 (hRep descriptor83.representative)

def descriptor84 : OrbitDescriptor := ⟨4, 1, false⟩

theorem checked84 : orbitPatternTransform descriptor84 (Generated.Chunk0030.pattern84) =
    orbitRepresentativePattern descriptor84.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf84 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0030.pattern84 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0030.pattern84) descriptor84 checked84 (hRep descriptor84.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0030.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0030.regionContext := by
  apply Generated.FunctionalChunk0030.valid
  · exact leaf82 hRep
  · exact leaf83 hRep
  · exact leaf84 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0030

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0031
def descriptor85 : OrbitDescriptor := ⟨28, 1, false⟩

theorem checked85 : orbitPatternTransform descriptor85 (Generated.Chunk0031.pattern85) =
    orbitRepresentativePattern descriptor85.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf85 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0031.pattern85 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0031.pattern85) descriptor85 checked85 (hRep descriptor85.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0031.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0031.regionContext := by
  apply Generated.FunctionalChunk0031.valid
  · exact leaf85 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0031
