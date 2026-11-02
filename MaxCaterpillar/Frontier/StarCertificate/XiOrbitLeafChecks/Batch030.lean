import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0240
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0241
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0242
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0243
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0244
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0245
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0246
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0247
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0240
def descriptor696 : OrbitDescriptor := ⟨9, 19, false⟩

theorem checked696 : orbitPatternTransform descriptor696 (Generated.Chunk0240.pattern696) =
    orbitRepresentativePattern descriptor696.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf696 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0240.pattern696 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0240.pattern696) descriptor696 checked696 (hRep descriptor696.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0240.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0240.regionContext := by
  apply Generated.FunctionalChunk0240.valid
  · exact leaf696 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0240

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0241
def descriptor697 : OrbitDescriptor := ⟨14, 19, false⟩

theorem checked697 : orbitPatternTransform descriptor697 (Generated.Chunk0241.pattern697) =
    orbitRepresentativePattern descriptor697.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf697 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0241.pattern697 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0241.pattern697) descriptor697 checked697 (hRep descriptor697.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0241.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0241.regionContext := by
  apply Generated.FunctionalChunk0241.valid
  · exact leaf697 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0241

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0242
def descriptor698 : OrbitDescriptor := ⟨17, 19, false⟩

theorem checked698 : orbitPatternTransform descriptor698 (Generated.Chunk0242.pattern698) =
    orbitRepresentativePattern descriptor698.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf698 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0242.pattern698 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0242.pattern698) descriptor698 checked698 (hRep descriptor698.representative)

def descriptor699 : OrbitDescriptor := ⟨19, 19, false⟩

theorem checked699 : orbitPatternTransform descriptor699 (Generated.Chunk0242.pattern699) =
    orbitRepresentativePattern descriptor699.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf699 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0242.pattern699 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0242.pattern699) descriptor699 checked699 (hRep descriptor699.representative)

def descriptor700 : OrbitDescriptor := ⟨20, 5, false⟩

theorem checked700 : orbitPatternTransform descriptor700 (Generated.Chunk0242.pattern700) =
    orbitRepresentativePattern descriptor700.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf700 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0242.pattern700 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0242.pattern700) descriptor700 checked700 (hRep descriptor700.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0242.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0242.regionContext := by
  apply Generated.FunctionalChunk0242.valid
  · exact leaf698 hRep
  · exact leaf699 hRep
  · exact leaf700 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0242

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0243
def descriptor701 : OrbitDescriptor := ⟨19, 22, false⟩

theorem checked701 : orbitPatternTransform descriptor701 (Generated.Chunk0243.pattern701) =
    orbitRepresentativePattern descriptor701.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf701 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0243.pattern701 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0243.pattern701) descriptor701 checked701 (hRep descriptor701.representative)

def descriptor702 : OrbitDescriptor := ⟨22, 19, false⟩

theorem checked702 : orbitPatternTransform descriptor702 (Generated.Chunk0243.pattern702) =
    orbitRepresentativePattern descriptor702.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf702 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0243.pattern702 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0243.pattern702) descriptor702 checked702 (hRep descriptor702.representative)

def descriptor703 : OrbitDescriptor := ⟨23, 5, false⟩

theorem checked703 : orbitPatternTransform descriptor703 (Generated.Chunk0243.pattern703) =
    orbitRepresentativePattern descriptor703.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf703 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0243.pattern703 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0243.pattern703) descriptor703 checked703 (hRep descriptor703.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0243.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0243.regionContext := by
  apply Generated.FunctionalChunk0243.valid
  · exact leaf701 hRep
  · exact leaf702 hRep
  · exact leaf703 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0243

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0244
def descriptor704 : OrbitDescriptor := ⟨20, 16, false⟩

theorem checked704 : orbitPatternTransform descriptor704 (Generated.Chunk0244.pattern704) =
    orbitRepresentativePattern descriptor704.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf704 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0244.pattern704 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0244.pattern704) descriptor704 checked704 (hRep descriptor704.representative)

def descriptor705 : OrbitDescriptor := ⟨23, 16, false⟩

theorem checked705 : orbitPatternTransform descriptor705 (Generated.Chunk0244.pattern705) =
    orbitRepresentativePattern descriptor705.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf705 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0244.pattern705 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0244.pattern705) descriptor705 checked705 (hRep descriptor705.representative)

def descriptor706 : OrbitDescriptor := ⟨24, 3, false⟩

theorem checked706 : orbitPatternTransform descriptor706 (Generated.Chunk0244.pattern706) =
    orbitRepresentativePattern descriptor706.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf706 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0244.pattern706 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0244.pattern706) descriptor706 checked706 (hRep descriptor706.representative)

def descriptor707 : OrbitDescriptor := ⟨25, 3, false⟩

theorem checked707 : orbitPatternTransform descriptor707 (Generated.Chunk0244.pattern707) =
    orbitRepresentativePattern descriptor707.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf707 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0244.pattern707 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0244.pattern707) descriptor707 checked707 (hRep descriptor707.representative)

def descriptor708 : OrbitDescriptor := ⟨26, 3, false⟩

theorem checked708 : orbitPatternTransform descriptor708 (Generated.Chunk0244.pattern708) =
    orbitRepresentativePattern descriptor708.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf708 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0244.pattern708 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0244.pattern708) descriptor708 checked708 (hRep descriptor708.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0244.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0244.regionContext := by
  apply Generated.FunctionalChunk0244.valid
  · exact leaf704 hRep
  · exact leaf705 hRep
  · exact leaf706 hRep
  · exact leaf707 hRep
  · exact leaf708 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0244

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0245
def descriptor709 : OrbitDescriptor := ⟨35, 3, false⟩

theorem checked709 : orbitPatternTransform descriptor709 (Generated.Chunk0245.pattern709) =
    orbitRepresentativePattern descriptor709.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf709 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0245.pattern709 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0245.pattern709) descriptor709 checked709 (hRep descriptor709.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0245.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0245.regionContext := by
  apply Generated.FunctionalChunk0245.valid
  · exact leaf709 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0245

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0246
def descriptor710 : OrbitDescriptor := ⟨54, 3, false⟩

theorem checked710 : orbitPatternTransform descriptor710 (Generated.Chunk0246.pattern710) =
    orbitRepresentativePattern descriptor710.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf710 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0246.pattern710 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0246.pattern710) descriptor710 checked710 (hRep descriptor710.representative)

def descriptor711 : OrbitDescriptor := ⟨58, 11, true⟩

theorem checked711 : orbitPatternTransform descriptor711 (Generated.Chunk0246.pattern711) =
    orbitRepresentativePattern descriptor711.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf711 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0246.pattern711 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0246.pattern711) descriptor711 checked711 (hRep descriptor711.representative)

def descriptor712 : OrbitDescriptor := ⟨45, 11, true⟩

theorem checked712 : orbitPatternTransform descriptor712 (Generated.Chunk0246.pattern712) =
    orbitRepresentativePattern descriptor712.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf712 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0246.pattern712 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0246.pattern712) descriptor712 checked712 (hRep descriptor712.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0246.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0246.regionContext := by
  apply Generated.FunctionalChunk0246.valid
  · exact leaf710 hRep
  · exact leaf711 hRep
  · exact leaf712 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0246

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0247
def descriptor713 : OrbitDescriptor := ⟨58, 10, true⟩

theorem checked713 : orbitPatternTransform descriptor713 (Generated.Chunk0247.pattern713) =
    orbitRepresentativePattern descriptor713.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf713 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0247.pattern713 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0247.pattern713) descriptor713 checked713 (hRep descriptor713.representative)

def descriptor714 : OrbitDescriptor := ⟨55, 10, true⟩

theorem checked714 : orbitPatternTransform descriptor714 (Generated.Chunk0247.pattern714) =
    orbitRepresentativePattern descriptor714.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf714 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0247.pattern714 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0247.pattern714) descriptor714 checked714 (hRep descriptor714.representative)

def descriptor715 : OrbitDescriptor := ⟨42, 11, true⟩

theorem checked715 : orbitPatternTransform descriptor715 (Generated.Chunk0247.pattern715) =
    orbitRepresentativePattern descriptor715.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf715 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0247.pattern715 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0247.pattern715) descriptor715 checked715 (hRep descriptor715.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0247.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0247.regionContext := by
  apply Generated.FunctionalChunk0247.valid
  · exact leaf713 hRep
  · exact leaf714 hRep
  · exact leaf715 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0247
