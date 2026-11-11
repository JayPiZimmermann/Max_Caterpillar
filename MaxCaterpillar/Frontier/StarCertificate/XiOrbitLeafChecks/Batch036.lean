import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0288
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0289
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0290
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0291
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0292
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0293
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0294
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0295
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0288
def descriptor832 : OrbitDescriptor := ⟨32, 16, true⟩

theorem checked832 : orbitPatternTransform descriptor832 (Generated.Chunk0288.pattern832) =
    orbitRepresentativePattern descriptor832.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf832 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0288.pattern832 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0288.pattern832) descriptor832 checked832 (hRep descriptor832.representative)

def descriptor833 : OrbitDescriptor := ⟨31, 16, true⟩

theorem checked833 : orbitPatternTransform descriptor833 (Generated.Chunk0288.pattern833) =
    orbitRepresentativePattern descriptor833.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf833 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0288.pattern833 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0288.pattern833) descriptor833 checked833 (hRep descriptor833.representative)

def descriptor834 : OrbitDescriptor := ⟨29, 22, true⟩

theorem checked834 : orbitPatternTransform descriptor834 (Generated.Chunk0288.pattern834) =
    orbitRepresentativePattern descriptor834.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf834 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0288.pattern834 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0288.pattern834) descriptor834 checked834 (hRep descriptor834.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0288.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0288.regionContext := by
  apply Generated.FunctionalChunk0288.valid
  · exact leaf832 hRep
  · exact leaf833 hRep
  · exact leaf834 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0288

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0289
def descriptor835 : OrbitDescriptor := ⟨30, 20, false⟩

theorem checked835 : orbitPatternTransform descriptor835 (Generated.Chunk0289.pattern835) =
    orbitRepresentativePattern descriptor835.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf835 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0289.pattern835 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0289.pattern835) descriptor835 checked835 (hRep descriptor835.representative)

def descriptor836 : OrbitDescriptor := ⟨32, 20, false⟩

theorem checked836 : orbitPatternTransform descriptor836 (Generated.Chunk0289.pattern836) =
    orbitRepresentativePattern descriptor836.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf836 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0289.pattern836 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0289.pattern836) descriptor836 checked836 (hRep descriptor836.representative)

def descriptor837 : OrbitDescriptor := ⟨33, 10, false⟩

theorem checked837 : orbitPatternTransform descriptor837 (Generated.Chunk0289.pattern837) =
    orbitRepresentativePattern descriptor837.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf837 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0289.pattern837 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0289.pattern837) descriptor837 checked837 (hRep descriptor837.representative)

def descriptor838 : OrbitDescriptor := ⟨34, 10, false⟩

theorem checked838 : orbitPatternTransform descriptor838 (Generated.Chunk0289.pattern838) =
    orbitRepresentativePattern descriptor838.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf838 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0289.pattern838 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0289.pattern838) descriptor838 checked838 (hRep descriptor838.representative)

def descriptor839 : OrbitDescriptor := ⟨35, 10, false⟩

theorem checked839 : orbitPatternTransform descriptor839 (Generated.Chunk0289.pattern839) =
    orbitRepresentativePattern descriptor839.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf839 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0289.pattern839 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0289.pattern839) descriptor839 checked839 (hRep descriptor839.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0289.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0289.regionContext := by
  apply Generated.FunctionalChunk0289.valid
  · exact leaf835 hRep
  · exact leaf836 hRep
  · exact leaf837 hRep
  · exact leaf838 hRep
  · exact leaf839 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0289

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0290
def descriptor840 : OrbitDescriptor := ⟨64, 13, true⟩

theorem checked840 : orbitPatternTransform descriptor840 (Generated.Chunk0290.pattern840) =
    orbitRepresentativePattern descriptor840.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf840 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0290.pattern840 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0290.pattern840) descriptor840 checked840 (hRep descriptor840.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0290.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0290.regionContext := by
  apply Generated.FunctionalChunk0290.valid
  · exact leaf840 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0290

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0291
def descriptor841 : OrbitDescriptor := ⟨30, 16, true⟩

theorem checked841 : orbitPatternTransform descriptor841 (Generated.Chunk0291.pattern841) =
    orbitRepresentativePattern descriptor841.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf841 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0291.pattern841 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0291.pattern841) descriptor841 checked841 (hRep descriptor841.representative)

def descriptor842 : OrbitDescriptor := ⟨29, 16, true⟩

theorem checked842 : orbitPatternTransform descriptor842 (Generated.Chunk0291.pattern842) =
    orbitRepresentativePattern descriptor842.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf842 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0291.pattern842 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0291.pattern842) descriptor842 checked842 (hRep descriptor842.representative)

def descriptor843 : OrbitDescriptor := ⟨28, 16, true⟩

theorem checked843 : orbitPatternTransform descriptor843 (Generated.Chunk0291.pattern843) =
    orbitRepresentativePattern descriptor843.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf843 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0291.pattern843 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0291.pattern843) descriptor843 checked843 (hRep descriptor843.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0291.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0291.regionContext := by
  apply Generated.FunctionalChunk0291.valid
  · exact leaf841 hRep
  · exact leaf842 hRep
  · exact leaf843 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0291

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0292
def descriptor844 : OrbitDescriptor := ⟨27, 16, false⟩

theorem checked844 : orbitPatternTransform descriptor844 (Generated.Chunk0292.pattern844) =
    orbitRepresentativePattern descriptor844.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf844 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0292.pattern844 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0292.pattern844) descriptor844 checked844 (hRep descriptor844.representative)

def descriptor845 : OrbitDescriptor := ⟨63, 12, false⟩

theorem checked845 : orbitPatternTransform descriptor845 (Generated.Chunk0292.pattern845) =
    orbitRepresentativePattern descriptor845.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf845 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0292.pattern845 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0292.pattern845) descriptor845 checked845 (hRep descriptor845.representative)

def descriptor846 : OrbitDescriptor := ⟨64, 12, false⟩

theorem checked846 : orbitPatternTransform descriptor846 (Generated.Chunk0292.pattern846) =
    orbitRepresentativePattern descriptor846.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf846 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0292.pattern846 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0292.pattern846) descriptor846 checked846 (hRep descriptor846.representative)

def descriptor847 : OrbitDescriptor := ⟨65, 12, false⟩

theorem checked847 : orbitPatternTransform descriptor847 (Generated.Chunk0292.pattern847) =
    orbitRepresentativePattern descriptor847.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf847 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0292.pattern847 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0292.pattern847) descriptor847 checked847 (hRep descriptor847.representative)

def descriptor848 : OrbitDescriptor := ⟨64, 18, true⟩

theorem checked848 : orbitPatternTransform descriptor848 (Generated.Chunk0292.pattern848) =
    orbitRepresentativePattern descriptor848.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf848 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0292.pattern848 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0292.pattern848) descriptor848 checked848 (hRep descriptor848.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0292.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0292.regionContext := by
  apply Generated.FunctionalChunk0292.valid
  · exact leaf844 hRep
  · exact leaf845 hRep
  · exact leaf846 hRep
  · exact leaf847 hRep
  · exact leaf848 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0292

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0293
def descriptor849 : OrbitDescriptor := ⟨63, 18, false⟩

theorem checked849 : orbitPatternTransform descriptor849 (Generated.Chunk0293.pattern849) =
    orbitRepresentativePattern descriptor849.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf849 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0293.pattern849 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0293.pattern849) descriptor849 checked849 (hRep descriptor849.representative)

def descriptor850 : OrbitDescriptor := ⟨66, 0, false⟩

theorem checked850 : orbitPatternTransform descriptor850 (Generated.Chunk0293.pattern850) =
    orbitRepresentativePattern descriptor850.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf850 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0293.pattern850 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0293.pattern850) descriptor850 checked850 (hRep descriptor850.representative)

def descriptor851 : OrbitDescriptor := ⟨63, 18, true⟩

theorem checked851 : orbitPatternTransform descriptor851 (Generated.Chunk0293.pattern851) =
    orbitRepresentativePattern descriptor851.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf851 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0293.pattern851 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0293.pattern851) descriptor851 checked851 (hRep descriptor851.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0293.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0293.regionContext := by
  apply Generated.FunctionalChunk0293.valid
  · exact leaf849 hRep
  · exact leaf850 hRep
  · exact leaf851 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0293

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0294
def descriptor852 : OrbitDescriptor := ⟨64, 18, false⟩

theorem checked852 : orbitPatternTransform descriptor852 (Generated.Chunk0294.pattern852) =
    orbitRepresentativePattern descriptor852.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf852 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0294.pattern852 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0294.pattern852) descriptor852 checked852 (hRep descriptor852.representative)

def descriptor853 : OrbitDescriptor := ⟨65, 18, false⟩

theorem checked853 : orbitPatternTransform descriptor853 (Generated.Chunk0294.pattern853) =
    orbitRepresentativePattern descriptor853.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf853 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0294.pattern853 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0294.pattern853) descriptor853 checked853 (hRep descriptor853.representative)

def descriptor854 : OrbitDescriptor := ⟨64, 12, true⟩

theorem checked854 : orbitPatternTransform descriptor854 (Generated.Chunk0294.pattern854) =
    orbitRepresentativePattern descriptor854.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf854 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0294.pattern854 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0294.pattern854) descriptor854 checked854 (hRep descriptor854.representative)

def descriptor855 : OrbitDescriptor := ⟨63, 12, true⟩

theorem checked855 : orbitPatternTransform descriptor855 (Generated.Chunk0294.pattern855) =
    orbitRepresentativePattern descriptor855.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf855 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0294.pattern855 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0294.pattern855) descriptor855 checked855 (hRep descriptor855.representative)

def descriptor856 : OrbitDescriptor := ⟨27, 16, true⟩

theorem checked856 : orbitPatternTransform descriptor856 (Generated.Chunk0294.pattern856) =
    orbitRepresentativePattern descriptor856.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf856 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0294.pattern856 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0294.pattern856) descriptor856 checked856 (hRep descriptor856.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0294.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0294.regionContext := by
  apply Generated.FunctionalChunk0294.valid
  · exact leaf852 hRep
  · exact leaf853 hRep
  · exact leaf854 hRep
  · exact leaf855 hRep
  · exact leaf856 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0294

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0295
def descriptor857 : OrbitDescriptor := ⟨28, 16, false⟩

theorem checked857 : orbitPatternTransform descriptor857 (Generated.Chunk0295.pattern857) =
    orbitRepresentativePattern descriptor857.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf857 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0295.pattern857 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0295.pattern857) descriptor857 checked857 (hRep descriptor857.representative)

def descriptor858 : OrbitDescriptor := ⟨29, 16, false⟩

theorem checked858 : orbitPatternTransform descriptor858 (Generated.Chunk0295.pattern858) =
    orbitRepresentativePattern descriptor858.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf858 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0295.pattern858 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0295.pattern858) descriptor858 checked858 (hRep descriptor858.representative)

def descriptor859 : OrbitDescriptor := ⟨30, 16, false⟩

theorem checked859 : orbitPatternTransform descriptor859 (Generated.Chunk0295.pattern859) =
    orbitRepresentativePattern descriptor859.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf859 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0295.pattern859 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0295.pattern859) descriptor859 checked859 (hRep descriptor859.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0295.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0295.regionContext := by
  apply Generated.FunctionalChunk0295.valid
  · exact leaf857 hRep
  · exact leaf858 hRep
  · exact leaf859 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0295
