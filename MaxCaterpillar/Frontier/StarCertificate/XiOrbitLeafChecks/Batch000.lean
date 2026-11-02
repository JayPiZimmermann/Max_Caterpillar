import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0000
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0001
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0002
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0003
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0004
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0005
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0006
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0007
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0000
def descriptor0 : OrbitDescriptor := ⟨0, 0, false⟩

theorem checked0 : orbitPatternTransform descriptor0 (Generated.Chunk0000.pattern0) =
    orbitRepresentativePattern descriptor0.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf0 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0000.pattern0 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0000.pattern0) descriptor0 checked0 (hRep descriptor0.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0000.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0000.regionContext := by
  apply Generated.FunctionalChunk0000.valid
  · exact leaf0 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0000

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0001
def descriptor1 : OrbitDescriptor := ⟨1, 0, false⟩

theorem checked1 : orbitPatternTransform descriptor1 (Generated.Chunk0001.pattern1) =
    orbitRepresentativePattern descriptor1.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf1 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0001.pattern1 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0001.pattern1) descriptor1 checked1 (hRep descriptor1.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0001.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0001.regionContext := by
  apply Generated.FunctionalChunk0001.valid
  · exact leaf1 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0001

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0002
def descriptor2 : OrbitDescriptor := ⟨2, 0, false⟩

theorem checked2 : orbitPatternTransform descriptor2 (Generated.Chunk0002.pattern2) =
    orbitRepresentativePattern descriptor2.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf2 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0002.pattern2 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0002.pattern2) descriptor2 checked2 (hRep descriptor2.representative)

def descriptor3 : OrbitDescriptor := ⟨3, 0, false⟩

theorem checked3 : orbitPatternTransform descriptor3 (Generated.Chunk0002.pattern3) =
    orbitRepresentativePattern descriptor3.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf3 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0002.pattern3 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0002.pattern3) descriptor3 checked3 (hRep descriptor3.representative)

def descriptor4 : OrbitDescriptor := ⟨4, 0, false⟩

theorem checked4 : orbitPatternTransform descriptor4 (Generated.Chunk0002.pattern4) =
    orbitRepresentativePattern descriptor4.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf4 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0002.pattern4 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0002.pattern4) descriptor4 checked4 (hRep descriptor4.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0002.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0002.regionContext := by
  apply Generated.FunctionalChunk0002.valid
  · exact leaf2 hRep
  · exact leaf3 hRep
  · exact leaf4 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0002

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0003
def descriptor5 : OrbitDescriptor := ⟨3, 2, false⟩

theorem checked5 : orbitPatternTransform descriptor5 (Generated.Chunk0003.pattern5) =
    orbitRepresentativePattern descriptor5.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf5 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0003.pattern5 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0003.pattern5) descriptor5 checked5 (hRep descriptor5.representative)

def descriptor6 : OrbitDescriptor := ⟨5, 0, false⟩

theorem checked6 : orbitPatternTransform descriptor6 (Generated.Chunk0003.pattern6) =
    orbitRepresentativePattern descriptor6.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf6 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0003.pattern6 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0003.pattern6) descriptor6 checked6 (hRep descriptor6.representative)

def descriptor7 : OrbitDescriptor := ⟨6, 0, false⟩

theorem checked7 : orbitPatternTransform descriptor7 (Generated.Chunk0003.pattern7) =
    orbitRepresentativePattern descriptor7.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf7 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0003.pattern7 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0003.pattern7) descriptor7 checked7 (hRep descriptor7.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0003.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0003.regionContext := by
  apply Generated.FunctionalChunk0003.valid
  · exact leaf5 hRep
  · exact leaf6 hRep
  · exact leaf7 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0003

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0004
def descriptor8 : OrbitDescriptor := ⟨4, 2, false⟩

theorem checked8 : orbitPatternTransform descriptor8 (Generated.Chunk0004.pattern8) =
    orbitRepresentativePattern descriptor8.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf8 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0004.pattern8 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0004.pattern8) descriptor8 checked8 (hRep descriptor8.representative)

def descriptor9 : OrbitDescriptor := ⟨6, 2, false⟩

theorem checked9 : orbitPatternTransform descriptor9 (Generated.Chunk0004.pattern9) =
    orbitRepresentativePattern descriptor9.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf9 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0004.pattern9 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0004.pattern9) descriptor9 checked9 (hRep descriptor9.representative)

def descriptor10 : OrbitDescriptor := ⟨7, 0, false⟩

theorem checked10 : orbitPatternTransform descriptor10 (Generated.Chunk0004.pattern10) =
    orbitRepresentativePattern descriptor10.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf10 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0004.pattern10 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0004.pattern10) descriptor10 checked10 (hRep descriptor10.representative)

def descriptor11 : OrbitDescriptor := ⟨8, 0, false⟩

theorem checked11 : orbitPatternTransform descriptor11 (Generated.Chunk0004.pattern11) =
    orbitRepresentativePattern descriptor11.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf11 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0004.pattern11 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0004.pattern11) descriptor11 checked11 (hRep descriptor11.representative)

def descriptor12 : OrbitDescriptor := ⟨9, 0, false⟩

theorem checked12 : orbitPatternTransform descriptor12 (Generated.Chunk0004.pattern12) =
    orbitRepresentativePattern descriptor12.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf12 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0004.pattern12 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0004.pattern12) descriptor12 checked12 (hRep descriptor12.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0004.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0004.regionContext := by
  apply Generated.FunctionalChunk0004.valid
  · exact leaf8 hRep
  · exact leaf9 hRep
  · exact leaf10 hRep
  · exact leaf11 hRep
  · exact leaf12 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0004

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0005
def descriptor13 : OrbitDescriptor := ⟨3, 8, false⟩

theorem checked13 : orbitPatternTransform descriptor13 (Generated.Chunk0005.pattern13) =
    orbitRepresentativePattern descriptor13.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf13 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0005.pattern13 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0005.pattern13) descriptor13 checked13 (hRep descriptor13.representative)

def descriptor14 : OrbitDescriptor := ⟨5, 6, false⟩

theorem checked14 : orbitPatternTransform descriptor14 (Generated.Chunk0005.pattern14) =
    orbitRepresentativePattern descriptor14.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf14 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0005.pattern14 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0005.pattern14) descriptor14 checked14 (hRep descriptor14.representative)

def descriptor15 : OrbitDescriptor := ⟨6, 6, false⟩

theorem checked15 : orbitPatternTransform descriptor15 (Generated.Chunk0005.pattern15) =
    orbitRepresentativePattern descriptor15.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf15 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0005.pattern15 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0005.pattern15) descriptor15 checked15 (hRep descriptor15.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0005.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0005.regionContext := by
  apply Generated.FunctionalChunk0005.valid
  · exact leaf13 hRep
  · exact leaf14 hRep
  · exact leaf15 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0005

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0006
def descriptor16 : OrbitDescriptor := ⟨5, 12, false⟩

theorem checked16 : orbitPatternTransform descriptor16 (Generated.Chunk0006.pattern16) =
    orbitRepresentativePattern descriptor16.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf16 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0006.pattern16 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0006.pattern16) descriptor16 checked16 (hRep descriptor16.representative)

def descriptor17 : OrbitDescriptor := ⟨10, 0, false⟩

theorem checked17 : orbitPatternTransform descriptor17 (Generated.Chunk0006.pattern17) =
    orbitRepresentativePattern descriptor17.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf17 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0006.pattern17 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0006.pattern17) descriptor17 checked17 (hRep descriptor17.representative)

def descriptor18 : OrbitDescriptor := ⟨11, 0, false⟩

theorem checked18 : orbitPatternTransform descriptor18 (Generated.Chunk0006.pattern18) =
    orbitRepresentativePattern descriptor18.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf18 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0006.pattern18 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0006.pattern18) descriptor18 checked18 (hRep descriptor18.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0006.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0006.regionContext := by
  apply Generated.FunctionalChunk0006.valid
  · exact leaf16 hRep
  · exact leaf17 hRep
  · exact leaf18 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0006

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0007
def descriptor19 : OrbitDescriptor := ⟨6, 12, false⟩

theorem checked19 : orbitPatternTransform descriptor19 (Generated.Chunk0007.pattern19) =
    orbitRepresentativePattern descriptor19.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf19 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0007.pattern19 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0007.pattern19) descriptor19 checked19 (hRep descriptor19.representative)

def descriptor20 : OrbitDescriptor := ⟨11, 2, false⟩

theorem checked20 : orbitPatternTransform descriptor20 (Generated.Chunk0007.pattern20) =
    orbitRepresentativePattern descriptor20.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf20 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0007.pattern20 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0007.pattern20) descriptor20 checked20 (hRep descriptor20.representative)

def descriptor21 : OrbitDescriptor := ⟨12, 0, false⟩

theorem checked21 : orbitPatternTransform descriptor21 (Generated.Chunk0007.pattern21) =
    orbitRepresentativePattern descriptor21.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf21 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0007.pattern21 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0007.pattern21) descriptor21 checked21 (hRep descriptor21.representative)

def descriptor22 : OrbitDescriptor := ⟨13, 0, false⟩

theorem checked22 : orbitPatternTransform descriptor22 (Generated.Chunk0007.pattern22) =
    orbitRepresentativePattern descriptor22.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf22 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0007.pattern22 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0007.pattern22) descriptor22 checked22 (hRep descriptor22.representative)

def descriptor23 : OrbitDescriptor := ⟨14, 0, false⟩

theorem checked23 : orbitPatternTransform descriptor23 (Generated.Chunk0007.pattern23) =
    orbitRepresentativePattern descriptor23.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf23 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0007.pattern23 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0007.pattern23) descriptor23 checked23 (hRep descriptor23.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0007.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0007.regionContext := by
  apply Generated.FunctionalChunk0007.valid
  · exact leaf19 hRep
  · exact leaf20 hRep
  · exact leaf21 hRep
  · exact leaf22 hRep
  · exact leaf23 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0007
