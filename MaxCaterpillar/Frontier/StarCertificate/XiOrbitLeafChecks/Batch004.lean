import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0032
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0033
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0034
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0035
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0036
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0037
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0038
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0039
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0032
def descriptor86 : OrbitDescriptor := ⟨36, 0, false⟩

theorem checked86 : orbitPatternTransform descriptor86 (Generated.Chunk0032.pattern86) =
    orbitRepresentativePattern descriptor86.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf86 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0032.pattern86 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0032.pattern86) descriptor86 checked86 (hRep descriptor86.representative)

def descriptor87 : OrbitDescriptor := ⟨37, 0, false⟩

theorem checked87 : orbitPatternTransform descriptor87 (Generated.Chunk0032.pattern87) =
    orbitRepresentativePattern descriptor87.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf87 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0032.pattern87 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0032.pattern87) descriptor87 checked87 (hRep descriptor87.representative)

def descriptor88 : OrbitDescriptor := ⟨38, 0, false⟩

theorem checked88 : orbitPatternTransform descriptor88 (Generated.Chunk0032.pattern88) =
    orbitRepresentativePattern descriptor88.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf88 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0032.pattern88 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0032.pattern88) descriptor88 checked88 (hRep descriptor88.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0032.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0032.regionContext := by
  apply Generated.FunctionalChunk0032.valid
  · exact leaf86 hRep
  · exact leaf87 hRep
  · exact leaf88 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0032

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0033
def descriptor89 : OrbitDescriptor := ⟨37, 6, false⟩

theorem checked89 : orbitPatternTransform descriptor89 (Generated.Chunk0033.pattern89) =
    orbitRepresentativePattern descriptor89.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf89 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0033.pattern89 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0033.pattern89) descriptor89 checked89 (hRep descriptor89.representative)

def descriptor90 : OrbitDescriptor := ⟨39, 0, false⟩

theorem checked90 : orbitPatternTransform descriptor90 (Generated.Chunk0033.pattern90) =
    orbitRepresentativePattern descriptor90.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf90 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0033.pattern90 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0033.pattern90) descriptor90 checked90 (hRep descriptor90.representative)

def descriptor91 : OrbitDescriptor := ⟨40, 0, false⟩

theorem checked91 : orbitPatternTransform descriptor91 (Generated.Chunk0033.pattern91) =
    orbitRepresentativePattern descriptor91.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf91 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0033.pattern91 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0033.pattern91) descriptor91 checked91 (hRep descriptor91.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0033.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0033.regionContext := by
  apply Generated.FunctionalChunk0033.valid
  · exact leaf89 hRep
  · exact leaf90 hRep
  · exact leaf91 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0033

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0034
def descriptor92 : OrbitDescriptor := ⟨38, 6, false⟩

theorem checked92 : orbitPatternTransform descriptor92 (Generated.Chunk0034.pattern92) =
    orbitRepresentativePattern descriptor92.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf92 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0034.pattern92 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0034.pattern92) descriptor92 checked92 (hRep descriptor92.representative)

def descriptor93 : OrbitDescriptor := ⟨40, 6, false⟩

theorem checked93 : orbitPatternTransform descriptor93 (Generated.Chunk0034.pattern93) =
    orbitRepresentativePattern descriptor93.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf93 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0034.pattern93 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0034.pattern93) descriptor93 checked93 (hRep descriptor93.representative)

def descriptor94 : OrbitDescriptor := ⟨41, 0, false⟩

theorem checked94 : orbitPatternTransform descriptor94 (Generated.Chunk0034.pattern94) =
    orbitRepresentativePattern descriptor94.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf94 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0034.pattern94 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0034.pattern94) descriptor94 checked94 (hRep descriptor94.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0034.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0034.regionContext := by
  apply Generated.FunctionalChunk0034.valid
  · exact leaf92 hRep
  · exact leaf93 hRep
  · exact leaf94 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0034

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0035
def descriptor95 : OrbitDescriptor := ⟨42, 0, false⟩

theorem checked95 : orbitPatternTransform descriptor95 (Generated.Chunk0035.pattern95) =
    orbitRepresentativePattern descriptor95.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf95 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0035.pattern95 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0035.pattern95) descriptor95 checked95 (hRep descriptor95.representative)

def descriptor96 : OrbitDescriptor := ⟨43, 0, false⟩

theorem checked96 : orbitPatternTransform descriptor96 (Generated.Chunk0035.pattern96) =
    orbitRepresentativePattern descriptor96.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf96 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0035.pattern96 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0035.pattern96) descriptor96 checked96 (hRep descriptor96.representative)

def descriptor97 : OrbitDescriptor := ⟨44, 0, false⟩

theorem checked97 : orbitPatternTransform descriptor97 (Generated.Chunk0035.pattern97) =
    orbitRepresentativePattern descriptor97.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf97 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0035.pattern97 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0035.pattern97) descriptor97 checked97 (hRep descriptor97.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0035.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0035.regionContext := by
  apply Generated.FunctionalChunk0035.valid
  · exact leaf95 hRep
  · exact leaf96 hRep
  · exact leaf97 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0035

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0036
def descriptor98 : OrbitDescriptor := ⟨45, 0, false⟩

theorem checked98 : orbitPatternTransform descriptor98 (Generated.Chunk0036.pattern98) =
    orbitRepresentativePattern descriptor98.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf98 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0036.pattern98 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0036.pattern98) descriptor98 checked98 (hRep descriptor98.representative)

def descriptor99 : OrbitDescriptor := ⟨46, 0, false⟩

theorem checked99 : orbitPatternTransform descriptor99 (Generated.Chunk0036.pattern99) =
    orbitRepresentativePattern descriptor99.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf99 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0036.pattern99 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0036.pattern99) descriptor99 checked99 (hRep descriptor99.representative)

def descriptor100 : OrbitDescriptor := ⟨47, 0, false⟩

theorem checked100 : orbitPatternTransform descriptor100 (Generated.Chunk0036.pattern100) =
    orbitRepresentativePattern descriptor100.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf100 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0036.pattern100 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0036.pattern100) descriptor100 checked100 (hRep descriptor100.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0036.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0036.regionContext := by
  apply Generated.FunctionalChunk0036.valid
  · exact leaf98 hRep
  · exact leaf99 hRep
  · exact leaf100 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0036

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0037
def descriptor101 : OrbitDescriptor := ⟨42, 6, false⟩

theorem checked101 : orbitPatternTransform descriptor101 (Generated.Chunk0037.pattern101) =
    orbitRepresentativePattern descriptor101.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf101 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0037.pattern101 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0037.pattern101) descriptor101 checked101 (hRep descriptor101.representative)

def descriptor102 : OrbitDescriptor := ⟨43, 6, false⟩

theorem checked102 : orbitPatternTransform descriptor102 (Generated.Chunk0037.pattern102) =
    orbitRepresentativePattern descriptor102.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf102 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0037.pattern102 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0037.pattern102) descriptor102 checked102 (hRep descriptor102.representative)

def descriptor103 : OrbitDescriptor := ⟨44, 6, false⟩

theorem checked103 : orbitPatternTransform descriptor103 (Generated.Chunk0037.pattern103) =
    orbitRepresentativePattern descriptor103.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf103 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0037.pattern103 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0037.pattern103) descriptor103 checked103 (hRep descriptor103.representative)

def descriptor104 : OrbitDescriptor := ⟨48, 0, false⟩

theorem checked104 : orbitPatternTransform descriptor104 (Generated.Chunk0037.pattern104) =
    orbitRepresentativePattern descriptor104.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf104 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0037.pattern104 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0037.pattern104) descriptor104 checked104 (hRep descriptor104.representative)

def descriptor105 : OrbitDescriptor := ⟨49, 0, false⟩

theorem checked105 : orbitPatternTransform descriptor105 (Generated.Chunk0037.pattern105) =
    orbitRepresentativePattern descriptor105.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf105 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0037.pattern105 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0037.pattern105) descriptor105 checked105 (hRep descriptor105.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0037.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0037.regionContext := by
  apply Generated.FunctionalChunk0037.valid
  · exact leaf101 hRep
  · exact leaf102 hRep
  · exact leaf103 hRep
  · exact leaf104 hRep
  · exact leaf105 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0037

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0038
def descriptor106 : OrbitDescriptor := ⟨45, 6, false⟩

theorem checked106 : orbitPatternTransform descriptor106 (Generated.Chunk0038.pattern106) =
    orbitRepresentativePattern descriptor106.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf106 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0038.pattern106 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0038.pattern106) descriptor106 checked106 (hRep descriptor106.representative)

def descriptor107 : OrbitDescriptor := ⟨46, 6, false⟩

theorem checked107 : orbitPatternTransform descriptor107 (Generated.Chunk0038.pattern107) =
    orbitRepresentativePattern descriptor107.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf107 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0038.pattern107 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0038.pattern107) descriptor107 checked107 (hRep descriptor107.representative)

def descriptor108 : OrbitDescriptor := ⟨47, 6, false⟩

theorem checked108 : orbitPatternTransform descriptor108 (Generated.Chunk0038.pattern108) =
    orbitRepresentativePattern descriptor108.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf108 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0038.pattern108 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0038.pattern108) descriptor108 checked108 (hRep descriptor108.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0038.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0038.regionContext := by
  apply Generated.FunctionalChunk0038.valid
  · exact leaf106 hRep
  · exact leaf107 hRep
  · exact leaf108 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0038

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0039
def descriptor109 : OrbitDescriptor := ⟨49, 6, false⟩

theorem checked109 : orbitPatternTransform descriptor109 (Generated.Chunk0039.pattern109) =
    orbitRepresentativePattern descriptor109.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf109 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0039.pattern109 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0039.pattern109) descriptor109 checked109 (hRep descriptor109.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0039.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0039.regionContext := by
  apply Generated.FunctionalChunk0039.valid
  · exact leaf109 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0039
