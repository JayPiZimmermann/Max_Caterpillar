import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0208
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0209
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0210
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0211
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0212
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0213
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0214
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0215
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0208
def descriptor604 : OrbitDescriptor := ⟨57, 14, true⟩

theorem checked604 : orbitPatternTransform descriptor604 (Generated.Chunk0208.pattern604) =
    orbitRepresentativePattern descriptor604.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf604 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0208.pattern604 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0208.pattern604) descriptor604 checked604 (hRep descriptor604.representative)

def descriptor605 : OrbitDescriptor := ⟨56, 14, true⟩

theorem checked605 : orbitPatternTransform descriptor605 (Generated.Chunk0208.pattern605) =
    orbitRepresentativePattern descriptor605.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf605 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0208.pattern605 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0208.pattern605) descriptor605 checked605 (hRep descriptor605.representative)

def descriptor606 : OrbitDescriptor := ⟨55, 14, true⟩

theorem checked606 : orbitPatternTransform descriptor606 (Generated.Chunk0208.pattern606) =
    orbitRepresentativePattern descriptor606.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf606 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0208.pattern606 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0208.pattern606) descriptor606 checked606 (hRep descriptor606.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0208.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0208.regionContext := by
  apply Generated.FunctionalChunk0208.valid
  · exact leaf604 hRep
  · exact leaf605 hRep
  · exact leaf606 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0208

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0209
def descriptor607 : OrbitDescriptor := ⟨44, 15, true⟩

theorem checked607 : orbitPatternTransform descriptor607 (Generated.Chunk0209.pattern607) =
    orbitRepresentativePattern descriptor607.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf607 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0209.pattern607 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0209.pattern607) descriptor607 checked607 (hRep descriptor607.representative)

def descriptor608 : OrbitDescriptor := ⟨43, 15, true⟩

theorem checked608 : orbitPatternTransform descriptor608 (Generated.Chunk0209.pattern608) =
    orbitRepresentativePattern descriptor608.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf608 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0209.pattern608 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0209.pattern608) descriptor608 checked608 (hRep descriptor608.representative)

def descriptor609 : OrbitDescriptor := ⟨42, 15, true⟩

theorem checked609 : orbitPatternTransform descriptor609 (Generated.Chunk0209.pattern609) =
    orbitRepresentativePattern descriptor609.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf609 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0209.pattern609 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0209.pattern609) descriptor609 checked609 (hRep descriptor609.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0209.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0209.regionContext := by
  apply Generated.FunctionalChunk0209.valid
  · exact leaf607 hRep
  · exact leaf608 hRep
  · exact leaf609 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0209

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0210
def descriptor610 : OrbitDescriptor := ⟨29, 15, true⟩

theorem checked610 : orbitPatternTransform descriptor610 (Generated.Chunk0210.pattern610) =
    orbitRepresentativePattern descriptor610.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf610 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0210.pattern610 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0210.pattern610) descriptor610 checked610 (hRep descriptor610.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0210.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0210.regionContext := by
  apply Generated.FunctionalChunk0210.valid
  · exact leaf610 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0210

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0211
def descriptor611 : OrbitDescriptor := ⟨6, 15, true⟩

theorem checked611 : orbitPatternTransform descriptor611 (Generated.Chunk0211.pattern611) =
    orbitRepresentativePattern descriptor611.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf611 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0211.pattern611 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0211.pattern611) descriptor611 checked611 (hRep descriptor611.representative)

def descriptor612 : OrbitDescriptor := ⟨5, 15, true⟩

theorem checked612 : orbitPatternTransform descriptor612 (Generated.Chunk0211.pattern612) =
    orbitRepresentativePattern descriptor612.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf612 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0211.pattern612 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0211.pattern612) descriptor612 checked612 (hRep descriptor612.representative)

def descriptor613 : OrbitDescriptor := ⟨3, 17, true⟩

theorem checked613 : orbitPatternTransform descriptor613 (Generated.Chunk0211.pattern613) =
    orbitRepresentativePattern descriptor613.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf613 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0211.pattern613 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0211.pattern613) descriptor613 checked613 (hRep descriptor613.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0211.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0211.regionContext := by
  apply Generated.FunctionalChunk0211.valid
  · exact leaf611 hRep
  · exact leaf612 hRep
  · exact leaf613 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0211

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0212
def descriptor614 : OrbitDescriptor := ⟨4, 16, false⟩

theorem checked614 : orbitPatternTransform descriptor614 (Generated.Chunk0212.pattern614) =
    orbitRepresentativePattern descriptor614.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf614 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0212.pattern614 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0212.pattern614) descriptor614 checked614 (hRep descriptor614.representative)

def descriptor615 : OrbitDescriptor := ⟨6, 16, false⟩

theorem checked615 : orbitPatternTransform descriptor615 (Generated.Chunk0212.pattern615) =
    orbitRepresentativePattern descriptor615.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf615 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0212.pattern615 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0212.pattern615) descriptor615 checked615 (hRep descriptor615.representative)

def descriptor616 : OrbitDescriptor := ⟨7, 13, false⟩

theorem checked616 : orbitPatternTransform descriptor616 (Generated.Chunk0212.pattern616) =
    orbitRepresentativePattern descriptor616.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf616 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0212.pattern616 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0212.pattern616) descriptor616 checked616 (hRep descriptor616.representative)

def descriptor617 : OrbitDescriptor := ⟨8, 13, false⟩

theorem checked617 : orbitPatternTransform descriptor617 (Generated.Chunk0212.pattern617) =
    orbitRepresentativePattern descriptor617.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf617 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0212.pattern617 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0212.pattern617) descriptor617 checked617 (hRep descriptor617.representative)

def descriptor618 : OrbitDescriptor := ⟨9, 13, false⟩

theorem checked618 : orbitPatternTransform descriptor618 (Generated.Chunk0212.pattern618) =
    orbitRepresentativePattern descriptor618.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf618 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0212.pattern618 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0212.pattern618) descriptor618 checked618 (hRep descriptor618.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0212.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0212.regionContext := by
  apply Generated.FunctionalChunk0212.valid
  · exact leaf614 hRep
  · exact leaf615 hRep
  · exact leaf616 hRep
  · exact leaf617 hRep
  · exact leaf618 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0212

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0213
def descriptor619 : OrbitDescriptor := ⟨30, 13, false⟩

theorem checked619 : orbitPatternTransform descriptor619 (Generated.Chunk0213.pattern619) =
    orbitRepresentativePattern descriptor619.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf619 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0213.pattern619 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0213.pattern619) descriptor619 checked619 (hRep descriptor619.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0213.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0213.regionContext := by
  apply Generated.FunctionalChunk0213.valid
  · exact leaf619 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0213

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0214
def descriptor620 : OrbitDescriptor := ⟨45, 13, false⟩

theorem checked620 : orbitPatternTransform descriptor620 (Generated.Chunk0214.pattern620) =
    orbitRepresentativePattern descriptor620.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf620 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0214.pattern620 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0214.pattern620) descriptor620 checked620 (hRep descriptor620.representative)

def descriptor621 : OrbitDescriptor := ⟨46, 13, false⟩

theorem checked621 : orbitPatternTransform descriptor621 (Generated.Chunk0214.pattern621) =
    orbitRepresentativePattern descriptor621.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf621 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0214.pattern621 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0214.pattern621) descriptor621 checked621 (hRep descriptor621.representative)

def descriptor622 : OrbitDescriptor := ⟨47, 13, false⟩

theorem checked622 : orbitPatternTransform descriptor622 (Generated.Chunk0214.pattern622) =
    orbitRepresentativePattern descriptor622.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf622 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0214.pattern622 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0214.pattern622) descriptor622 checked622 (hRep descriptor622.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0214.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0214.regionContext := by
  apply Generated.FunctionalChunk0214.valid
  · exact leaf620 hRep
  · exact leaf621 hRep
  · exact leaf622 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0214

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0215
def descriptor623 : OrbitDescriptor := ⟨58, 13, false⟩

theorem checked623 : orbitPatternTransform descriptor623 (Generated.Chunk0215.pattern623) =
    orbitRepresentativePattern descriptor623.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf623 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0215.pattern623 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0215.pattern623) descriptor623 checked623 (hRep descriptor623.representative)

def descriptor624 : OrbitDescriptor := ⟨59, 13, false⟩

theorem checked624 : orbitPatternTransform descriptor624 (Generated.Chunk0215.pattern624) =
    orbitRepresentativePattern descriptor624.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf624 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0215.pattern624 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0215.pattern624) descriptor624 checked624 (hRep descriptor624.representative)

def descriptor625 : OrbitDescriptor := ⟨60, 13, false⟩

theorem checked625 : orbitPatternTransform descriptor625 (Generated.Chunk0215.pattern625) =
    orbitRepresentativePattern descriptor625.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf625 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0215.pattern625 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0215.pattern625) descriptor625 checked625 (hRep descriptor625.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0215.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0215.regionContext := by
  apply Generated.FunctionalChunk0215.valid
  · exact leaf623 hRep
  · exact leaf624 hRep
  · exact leaf625 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0215
