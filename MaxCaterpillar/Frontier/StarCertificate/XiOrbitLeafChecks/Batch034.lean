import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0272
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0273
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0274
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0275
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0276
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0277
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0278
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0279
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0272
def descriptor792 : OrbitDescriptor := ⟨45, 8, true⟩

theorem checked792 : orbitPatternTransform descriptor792 (Generated.Chunk0272.pattern792) =
    orbitRepresentativePattern descriptor792.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf792 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0272.pattern792 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0272.pattern792) descriptor792 checked792 (hRep descriptor792.representative)

def descriptor793 : OrbitDescriptor := ⟨42, 8, true⟩

theorem checked793 : orbitPatternTransform descriptor793 (Generated.Chunk0272.pattern793) =
    orbitRepresentativePattern descriptor793.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf793 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0272.pattern793 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0272.pattern793) descriptor793 checked793 (hRep descriptor793.representative)

def descriptor794 : OrbitDescriptor := ⟨38, 8, true⟩

theorem checked794 : orbitPatternTransform descriptor794 (Generated.Chunk0272.pattern794) =
    orbitRepresentativePattern descriptor794.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf794 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0272.pattern794 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0272.pattern794) descriptor794 checked794 (hRep descriptor794.representative)

def descriptor795 : OrbitDescriptor := ⟨37, 8, true⟩

theorem checked795 : orbitPatternTransform descriptor795 (Generated.Chunk0272.pattern795) =
    orbitRepresentativePattern descriptor795.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf795 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0272.pattern795 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0272.pattern795) descriptor795 checked795 (hRep descriptor795.representative)

def descriptor796 : OrbitDescriptor := ⟨36, 8, true⟩

theorem checked796 : orbitPatternTransform descriptor796 (Generated.Chunk0272.pattern796) =
    orbitRepresentativePattern descriptor796.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf796 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0272.pattern796 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0272.pattern796) descriptor796 checked796 (hRep descriptor796.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0272.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0272.regionContext := by
  apply Generated.FunctionalChunk0272.valid
  · exact leaf792 hRep
  · exact leaf793 hRep
  · exact leaf794 hRep
  · exact leaf795 hRep
  · exact leaf796 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0272

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0273
def descriptor797 : OrbitDescriptor := ⟨28, 9, true⟩

theorem checked797 : orbitPatternTransform descriptor797 (Generated.Chunk0273.pattern797) =
    orbitRepresentativePattern descriptor797.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf797 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0273.pattern797 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0273.pattern797) descriptor797 checked797 (hRep descriptor797.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0273.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0273.regionContext := by
  apply Generated.FunctionalChunk0273.valid
  · exact leaf797 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0273

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0274
def descriptor798 : OrbitDescriptor := ⟨4, 9, true⟩

theorem checked798 : orbitPatternTransform descriptor798 (Generated.Chunk0274.pattern798) =
    orbitRepresentativePattern descriptor798.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf798 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0274.pattern798 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0274.pattern798) descriptor798 checked798 (hRep descriptor798.representative)

def descriptor799 : OrbitDescriptor := ⟨3, 9, true⟩

theorem checked799 : orbitPatternTransform descriptor799 (Generated.Chunk0274.pattern799) =
    orbitRepresentativePattern descriptor799.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf799 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0274.pattern799 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0274.pattern799) descriptor799 checked799 (hRep descriptor799.representative)

def descriptor800 : OrbitDescriptor := ⟨2, 9, true⟩

theorem checked800 : orbitPatternTransform descriptor800 (Generated.Chunk0274.pattern800) =
    orbitRepresentativePattern descriptor800.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf800 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0274.pattern800 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0274.pattern800) descriptor800 checked800 (hRep descriptor800.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0274.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0274.regionContext := by
  apply Generated.FunctionalChunk0274.valid
  · exact leaf798 hRep
  · exact leaf799 hRep
  · exact leaf800 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0274

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0275
def descriptor801 : OrbitDescriptor := ⟨1, 9, false⟩

theorem checked801 : orbitPatternTransform descriptor801 (Generated.Chunk0275.pattern801) =
    orbitRepresentativePattern descriptor801.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf801 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0275.pattern801 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0275.pattern801) descriptor801 checked801 (hRep descriptor801.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0275.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0275.regionContext := by
  apply Generated.FunctionalChunk0275.valid
  · exact leaf801 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0275

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0276
def descriptor802 : OrbitDescriptor := ⟨27, 8, false⟩

theorem checked802 : orbitPatternTransform descriptor802 (Generated.Chunk0276.pattern802) =
    orbitRepresentativePattern descriptor802.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf802 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0276.pattern802 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0276.pattern802) descriptor802 checked802 (hRep descriptor802.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0276.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0276.regionContext := by
  apply Generated.FunctionalChunk0276.valid
  · exact leaf802 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0276

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0277
def descriptor803 : OrbitDescriptor := ⟨28, 8, false⟩

theorem checked803 : orbitPatternTransform descriptor803 (Generated.Chunk0277.pattern803) =
    orbitRepresentativePattern descriptor803.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf803 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0277.pattern803 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0277.pattern803) descriptor803 checked803 (hRep descriptor803.representative)

def descriptor804 : OrbitDescriptor := ⟨29, 8, false⟩

theorem checked804 : orbitPatternTransform descriptor804 (Generated.Chunk0277.pattern804) =
    orbitRepresentativePattern descriptor804.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf804 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0277.pattern804 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0277.pattern804) descriptor804 checked804 (hRep descriptor804.representative)

def descriptor805 : OrbitDescriptor := ⟨30, 8, false⟩

theorem checked805 : orbitPatternTransform descriptor805 (Generated.Chunk0277.pattern805) =
    orbitRepresentativePattern descriptor805.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf805 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0277.pattern805 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0277.pattern805) descriptor805 checked805 (hRep descriptor805.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0277.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0277.regionContext := by
  apply Generated.FunctionalChunk0277.valid
  · exact leaf803 hRep
  · exact leaf804 hRep
  · exact leaf805 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0277

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0278
def descriptor806 : OrbitDescriptor := ⟨29, 14, false⟩

theorem checked806 : orbitPatternTransform descriptor806 (Generated.Chunk0278.pattern806) =
    orbitRepresentativePattern descriptor806.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf806 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0278.pattern806 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0278.pattern806) descriptor806 checked806 (hRep descriptor806.representative)

def descriptor807 : OrbitDescriptor := ⟨31, 8, false⟩

theorem checked807 : orbitPatternTransform descriptor807 (Generated.Chunk0278.pattern807) =
    orbitRepresentativePattern descriptor807.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf807 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0278.pattern807 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0278.pattern807) descriptor807 checked807 (hRep descriptor807.representative)

def descriptor808 : OrbitDescriptor := ⟨32, 8, false⟩

theorem checked808 : orbitPatternTransform descriptor808 (Generated.Chunk0278.pattern808) =
    orbitRepresentativePattern descriptor808.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf808 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0278.pattern808 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0278.pattern808) descriptor808 checked808 (hRep descriptor808.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0278.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0278.regionContext := by
  apply Generated.FunctionalChunk0278.valid
  · exact leaf806 hRep
  · exact leaf807 hRep
  · exact leaf808 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0278

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0279
def descriptor809 : OrbitDescriptor := ⟨30, 14, false⟩

theorem checked809 : orbitPatternTransform descriptor809 (Generated.Chunk0279.pattern809) =
    orbitRepresentativePattern descriptor809.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf809 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0279.pattern809 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0279.pattern809) descriptor809 checked809 (hRep descriptor809.representative)

def descriptor810 : OrbitDescriptor := ⟨32, 14, false⟩

theorem checked810 : orbitPatternTransform descriptor810 (Generated.Chunk0279.pattern810) =
    orbitRepresentativePattern descriptor810.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf810 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0279.pattern810 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0279.pattern810) descriptor810 checked810 (hRep descriptor810.representative)

def descriptor811 : OrbitDescriptor := ⟨33, 8, false⟩

theorem checked811 : orbitPatternTransform descriptor811 (Generated.Chunk0279.pattern811) =
    orbitRepresentativePattern descriptor811.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf811 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0279.pattern811 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0279.pattern811) descriptor811 checked811 (hRep descriptor811.representative)

def descriptor812 : OrbitDescriptor := ⟨34, 8, false⟩

theorem checked812 : orbitPatternTransform descriptor812 (Generated.Chunk0279.pattern812) =
    orbitRepresentativePattern descriptor812.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf812 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0279.pattern812 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0279.pattern812) descriptor812 checked812 (hRep descriptor812.representative)

def descriptor813 : OrbitDescriptor := ⟨35, 8, false⟩

theorem checked813 : orbitPatternTransform descriptor813 (Generated.Chunk0279.pattern813) =
    orbitRepresentativePattern descriptor813.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf813 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0279.pattern813 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0279.pattern813) descriptor813 checked813 (hRep descriptor813.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0279.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0279.regionContext := by
  apply Generated.FunctionalChunk0279.valid
  · exact leaf809 hRep
  · exact leaf810 hRep
  · exact leaf811 hRep
  · exact leaf812 hRep
  · exact leaf813 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0279
