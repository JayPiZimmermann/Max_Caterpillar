import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0256
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0257
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0258
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0259
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0260
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0261
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0262
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0263
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0256
def descriptor742 : OrbitDescriptor := ⟨54, 5, false⟩

theorem checked742 : orbitPatternTransform descriptor742 (Generated.Chunk0256.pattern742) =
    orbitRepresentativePattern descriptor742.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf742 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0256.pattern742 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0256.pattern742) descriptor742 checked742 (hRep descriptor742.representative)

def descriptor743 : OrbitDescriptor := ⟨58, 9, true⟩

theorem checked743 : orbitPatternTransform descriptor743 (Generated.Chunk0256.pattern743) =
    orbitRepresentativePattern descriptor743.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf743 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0256.pattern743 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0256.pattern743) descriptor743 checked743 (hRep descriptor743.representative)

def descriptor744 : OrbitDescriptor := ⟨45, 9, true⟩

theorem checked744 : orbitPatternTransform descriptor744 (Generated.Chunk0256.pattern744) =
    orbitRepresentativePattern descriptor744.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf744 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0256.pattern744 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0256.pattern744) descriptor744 checked744 (hRep descriptor744.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0256.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0256.regionContext := by
  apply Generated.FunctionalChunk0256.valid
  · exact leaf742 hRep
  · exact leaf743 hRep
  · exact leaf744 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0256

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0257
def descriptor745 : OrbitDescriptor := ⟨30, 9, true⟩

theorem checked745 : orbitPatternTransform descriptor745 (Generated.Chunk0257.pattern745) =
    orbitRepresentativePattern descriptor745.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf745 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0257.pattern745 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0257.pattern745) descriptor745 checked745 (hRep descriptor745.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0257.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0257.regionContext := by
  apply Generated.FunctionalChunk0257.valid
  · exact leaf745 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0257

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0258
def descriptor746 : OrbitDescriptor := ⟨9, 9, true⟩

theorem checked746 : orbitPatternTransform descriptor746 (Generated.Chunk0258.pattern746) =
    orbitRepresentativePattern descriptor746.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf746 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0258.pattern746 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0258.pattern746) descriptor746 checked746 (hRep descriptor746.representative)

def descriptor747 : OrbitDescriptor := ⟨8, 9, true⟩

theorem checked747 : orbitPatternTransform descriptor747 (Generated.Chunk0258.pattern747) =
    orbitRepresentativePattern descriptor747.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf747 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0258.pattern747 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0258.pattern747) descriptor747 checked747 (hRep descriptor747.representative)

def descriptor748 : OrbitDescriptor := ⟨7, 9, true⟩

theorem checked748 : orbitPatternTransform descriptor748 (Generated.Chunk0258.pattern748) =
    orbitRepresentativePattern descriptor748.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf748 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0258.pattern748 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0258.pattern748) descriptor748 checked748 (hRep descriptor748.representative)

def descriptor749 : OrbitDescriptor := ⟨6, 11, true⟩

theorem checked749 : orbitPatternTransform descriptor749 (Generated.Chunk0258.pattern749) =
    orbitRepresentativePattern descriptor749.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf749 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0258.pattern749 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0258.pattern749) descriptor749 checked749 (hRep descriptor749.representative)

def descriptor750 : OrbitDescriptor := ⟨4, 11, true⟩

theorem checked750 : orbitPatternTransform descriptor750 (Generated.Chunk0258.pattern750) =
    orbitRepresentativePattern descriptor750.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf750 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0258.pattern750 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0258.pattern750) descriptor750 checked750 (hRep descriptor750.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0258.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0258.regionContext := by
  apply Generated.FunctionalChunk0258.valid
  · exact leaf746 hRep
  · exact leaf747 hRep
  · exact leaf748 hRep
  · exact leaf749 hRep
  · exact leaf750 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0258

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0259
def descriptor751 : OrbitDescriptor := ⟨58, 19, false⟩

theorem checked751 : orbitPatternTransform descriptor751 (Generated.Chunk0259.pattern751) =
    orbitRepresentativePattern descriptor751.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf751 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0259.pattern751 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0259.pattern751) descriptor751 checked751 (hRep descriptor751.representative)

def descriptor752 : OrbitDescriptor := ⟨59, 19, false⟩

theorem checked752 : orbitPatternTransform descriptor752 (Generated.Chunk0259.pattern752) =
    orbitRepresentativePattern descriptor752.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf752 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0259.pattern752 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0259.pattern752) descriptor752 checked752 (hRep descriptor752.representative)

def descriptor753 : OrbitDescriptor := ⟨60, 19, false⟩

theorem checked753 : orbitPatternTransform descriptor753 (Generated.Chunk0259.pattern753) =
    orbitRepresentativePattern descriptor753.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf753 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0259.pattern753 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0259.pattern753) descriptor753 checked753 (hRep descriptor753.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0259.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0259.regionContext := by
  apply Generated.FunctionalChunk0259.valid
  · exact leaf751 hRep
  · exact leaf752 hRep
  · exact leaf753 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0259

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0260
def descriptor754 : OrbitDescriptor := ⟨61, 19, false⟩

theorem checked754 : orbitPatternTransform descriptor754 (Generated.Chunk0260.pattern754) =
    orbitRepresentativePattern descriptor754.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf754 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0260.pattern754 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0260.pattern754) descriptor754 checked754 (hRep descriptor754.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0260.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0260.regionContext := by
  apply Generated.FunctionalChunk0260.valid
  · exact leaf754 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0260

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0261
def descriptor755 : OrbitDescriptor := ⟨60, 8, true⟩

theorem checked755 : orbitPatternTransform descriptor755 (Generated.Chunk0261.pattern755) =
    orbitRepresentativePattern descriptor755.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf755 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0261.pattern755 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0261.pattern755) descriptor755 checked755 (hRep descriptor755.representative)

def descriptor756 : OrbitDescriptor := ⟨57, 8, true⟩

theorem checked756 : orbitPatternTransform descriptor756 (Generated.Chunk0261.pattern756) =
    orbitRepresentativePattern descriptor756.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf756 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0261.pattern756 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0261.pattern756) descriptor756 checked756 (hRep descriptor756.representative)

def descriptor757 : OrbitDescriptor := ⟨44, 9, true⟩

theorem checked757 : orbitPatternTransform descriptor757 (Generated.Chunk0261.pattern757) =
    orbitRepresentativePattern descriptor757.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf757 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0261.pattern757 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0261.pattern757) descriptor757 checked757 (hRep descriptor757.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0261.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0261.regionContext := by
  apply Generated.FunctionalChunk0261.valid
  · exact leaf755 hRep
  · exact leaf756 hRep
  · exact leaf757 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0261

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0262
def descriptor758 : OrbitDescriptor := ⟨59, 8, true⟩

theorem checked758 : orbitPatternTransform descriptor758 (Generated.Chunk0262.pattern758) =
    orbitRepresentativePattern descriptor758.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf758 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0262.pattern758 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0262.pattern758) descriptor758 checked758 (hRep descriptor758.representative)

def descriptor759 : OrbitDescriptor := ⟨56, 8, true⟩

theorem checked759 : orbitPatternTransform descriptor759 (Generated.Chunk0262.pattern759) =
    orbitRepresentativePattern descriptor759.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf759 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0262.pattern759 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0262.pattern759) descriptor759 checked759 (hRep descriptor759.representative)

def descriptor760 : OrbitDescriptor := ⟨43, 9, true⟩

theorem checked760 : orbitPatternTransform descriptor760 (Generated.Chunk0262.pattern760) =
    orbitRepresentativePattern descriptor760.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf760 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0262.pattern760 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0262.pattern760) descriptor760 checked760 (hRep descriptor760.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0262.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0262.regionContext := by
  apply Generated.FunctionalChunk0262.valid
  · exact leaf758 hRep
  · exact leaf759 hRep
  · exact leaf760 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0262

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0263
def descriptor761 : OrbitDescriptor := ⟨58, 8, true⟩

theorem checked761 : orbitPatternTransform descriptor761 (Generated.Chunk0263.pattern761) =
    orbitRepresentativePattern descriptor761.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf761 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0263.pattern761 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0263.pattern761) descriptor761 checked761 (hRep descriptor761.representative)

def descriptor762 : OrbitDescriptor := ⟨55, 8, true⟩

theorem checked762 : orbitPatternTransform descriptor762 (Generated.Chunk0263.pattern762) =
    orbitRepresentativePattern descriptor762.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf762 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0263.pattern762 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0263.pattern762) descriptor762 checked762 (hRep descriptor762.representative)

def descriptor763 : OrbitDescriptor := ⟨42, 9, true⟩

theorem checked763 : orbitPatternTransform descriptor763 (Generated.Chunk0263.pattern763) =
    orbitRepresentativePattern descriptor763.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf763 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0263.pattern763 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0263.pattern763) descriptor763 checked763 (hRep descriptor763.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0263.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0263.regionContext := by
  apply Generated.FunctionalChunk0263.valid
  · exact leaf761 hRep
  · exact leaf762 hRep
  · exact leaf763 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0263
