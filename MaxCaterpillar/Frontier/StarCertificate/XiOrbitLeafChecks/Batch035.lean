import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0280
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0281
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0282
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0283
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0284
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0285
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0286
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0287
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0280
def descriptor814 : OrbitDescriptor := ⟨27, 10, false⟩

theorem checked814 : orbitPatternTransform descriptor814 (Generated.Chunk0280.pattern814) =
    orbitRepresentativePattern descriptor814.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf814 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0280.pattern814 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0280.pattern814) descriptor814 checked814 (hRep descriptor814.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0280.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0280.regionContext := by
  apply Generated.FunctionalChunk0280.valid
  · exact leaf814 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0280

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0281
def descriptor815 : OrbitDescriptor := ⟨63, 6, false⟩

theorem checked815 : orbitPatternTransform descriptor815 (Generated.Chunk0281.pattern815) =
    orbitRepresentativePattern descriptor815.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf815 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0281.pattern815 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0281.pattern815) descriptor815 checked815 (hRep descriptor815.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0281.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0281.regionContext := by
  apply Generated.FunctionalChunk0281.valid
  · exact leaf815 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0281

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0282
def descriptor816 : OrbitDescriptor := ⟨64, 6, false⟩

theorem checked816 : orbitPatternTransform descriptor816 (Generated.Chunk0282.pattern816) =
    orbitRepresentativePattern descriptor816.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf816 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0282.pattern816 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0282.pattern816) descriptor816 checked816 (hRep descriptor816.representative)

def descriptor817 : OrbitDescriptor := ⟨65, 6, false⟩

theorem checked817 : orbitPatternTransform descriptor817 (Generated.Chunk0282.pattern817) =
    orbitRepresentativePattern descriptor817.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf817 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0282.pattern817 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0282.pattern817) descriptor817 checked817 (hRep descriptor817.representative)

def descriptor818 : OrbitDescriptor := ⟨64, 19, true⟩

theorem checked818 : orbitPatternTransform descriptor818 (Generated.Chunk0282.pattern818) =
    orbitRepresentativePattern descriptor818.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf818 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0282.pattern818 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0282.pattern818) descriptor818 checked818 (hRep descriptor818.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0282.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0282.regionContext := by
  apply Generated.FunctionalChunk0282.valid
  · exact leaf816 hRep
  · exact leaf817 hRep
  · exact leaf818 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0282

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0283
def descriptor819 : OrbitDescriptor := ⟨28, 10, false⟩

theorem checked819 : orbitPatternTransform descriptor819 (Generated.Chunk0283.pattern819) =
    orbitRepresentativePattern descriptor819.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf819 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0283.pattern819 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0283.pattern819) descriptor819 checked819 (hRep descriptor819.representative)

def descriptor820 : OrbitDescriptor := ⟨29, 10, false⟩

theorem checked820 : orbitPatternTransform descriptor820 (Generated.Chunk0283.pattern820) =
    orbitRepresentativePattern descriptor820.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf820 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0283.pattern820 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0283.pattern820) descriptor820 checked820 (hRep descriptor820.representative)

def descriptor821 : OrbitDescriptor := ⟨30, 10, false⟩

theorem checked821 : orbitPatternTransform descriptor821 (Generated.Chunk0283.pattern821) =
    orbitRepresentativePattern descriptor821.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf821 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0283.pattern821 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0283.pattern821) descriptor821 checked821 (hRep descriptor821.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0283.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0283.regionContext := by
  apply Generated.FunctionalChunk0283.valid
  · exact leaf819 hRep
  · exact leaf820 hRep
  · exact leaf821 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0283

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0284
def descriptor822 : OrbitDescriptor := ⟨64, 7, false⟩

theorem checked822 : orbitPatternTransform descriptor822 (Generated.Chunk0284.pattern822) =
    orbitRepresentativePattern descriptor822.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf822 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0284.pattern822 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0284.pattern822) descriptor822 checked822 (hRep descriptor822.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0284.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0284.regionContext := by
  apply Generated.FunctionalChunk0284.valid
  · exact leaf822 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0284

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0285
def descriptor823 : OrbitDescriptor := ⟨35, 16, true⟩

theorem checked823 : orbitPatternTransform descriptor823 (Generated.Chunk0285.pattern823) =
    orbitRepresentativePattern descriptor823.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf823 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0285.pattern823 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0285.pattern823) descriptor823 checked823 (hRep descriptor823.representative)

def descriptor824 : OrbitDescriptor := ⟨34, 16, true⟩

theorem checked824 : orbitPatternTransform descriptor824 (Generated.Chunk0285.pattern824) =
    orbitRepresentativePattern descriptor824.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf824 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0285.pattern824 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0285.pattern824) descriptor824 checked824 (hRep descriptor824.representative)

def descriptor825 : OrbitDescriptor := ⟨33, 16, true⟩

theorem checked825 : orbitPatternTransform descriptor825 (Generated.Chunk0285.pattern825) =
    orbitRepresentativePattern descriptor825.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf825 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0285.pattern825 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0285.pattern825) descriptor825 checked825 (hRep descriptor825.representative)

def descriptor826 : OrbitDescriptor := ⟨32, 22, true⟩

theorem checked826 : orbitPatternTransform descriptor826 (Generated.Chunk0285.pattern826) =
    orbitRepresentativePattern descriptor826.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf826 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0285.pattern826 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0285.pattern826) descriptor826 checked826 (hRep descriptor826.representative)

def descriptor827 : OrbitDescriptor := ⟨30, 22, true⟩

theorem checked827 : orbitPatternTransform descriptor827 (Generated.Chunk0285.pattern827) =
    orbitRepresentativePattern descriptor827.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf827 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0285.pattern827 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0285.pattern827) descriptor827 checked827 (hRep descriptor827.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0285.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0285.regionContext := by
  apply Generated.FunctionalChunk0285.valid
  · exact leaf823 hRep
  · exact leaf824 hRep
  · exact leaf825 hRep
  · exact leaf826 hRep
  · exact leaf827 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0285

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0286
def descriptor828 : OrbitDescriptor := ⟨29, 20, false⟩

theorem checked828 : orbitPatternTransform descriptor828 (Generated.Chunk0286.pattern828) =
    orbitRepresentativePattern descriptor828.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf828 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0286.pattern828 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0286.pattern828) descriptor828 checked828 (hRep descriptor828.representative)

def descriptor829 : OrbitDescriptor := ⟨31, 10, false⟩

theorem checked829 : orbitPatternTransform descriptor829 (Generated.Chunk0286.pattern829) =
    orbitRepresentativePattern descriptor829.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf829 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0286.pattern829 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0286.pattern829) descriptor829 checked829 (hRep descriptor829.representative)

def descriptor830 : OrbitDescriptor := ⟨32, 10, false⟩

theorem checked830 : orbitPatternTransform descriptor830 (Generated.Chunk0286.pattern830) =
    orbitRepresentativePattern descriptor830.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf830 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0286.pattern830 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0286.pattern830) descriptor830 checked830 (hRep descriptor830.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0286.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0286.regionContext := by
  apply Generated.FunctionalChunk0286.valid
  · exact leaf828 hRep
  · exact leaf829 hRep
  · exact leaf830 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0286

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0287
def descriptor831 : OrbitDescriptor := ⟨65, 7, false⟩

theorem checked831 : orbitPatternTransform descriptor831 (Generated.Chunk0287.pattern831) =
    orbitRepresentativePattern descriptor831.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf831 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0287.pattern831 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0287.pattern831) descriptor831 checked831 (hRep descriptor831.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0287.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0287.regionContext := by
  apply Generated.FunctionalChunk0287.valid
  · exact leaf831 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0287
