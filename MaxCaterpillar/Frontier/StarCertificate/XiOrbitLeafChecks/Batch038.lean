import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0304
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0305
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0306
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0307
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0308
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0309
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0310
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0311
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0304
def descriptor882 : OrbitDescriptor := ⟨64, 19, false⟩

theorem checked882 : orbitPatternTransform descriptor882 (Generated.Chunk0304.pattern882) =
    orbitRepresentativePattern descriptor882.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf882 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0304.pattern882 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0304.pattern882) descriptor882 checked882 (hRep descriptor882.representative)

def descriptor883 : OrbitDescriptor := ⟨65, 19, false⟩

theorem checked883 : orbitPatternTransform descriptor883 (Generated.Chunk0304.pattern883) =
    orbitRepresentativePattern descriptor883.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf883 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0304.pattern883 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0304.pattern883) descriptor883 checked883 (hRep descriptor883.representative)

def descriptor884 : OrbitDescriptor := ⟨64, 6, true⟩

theorem checked884 : orbitPatternTransform descriptor884 (Generated.Chunk0304.pattern884) =
    orbitRepresentativePattern descriptor884.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf884 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0304.pattern884 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0304.pattern884) descriptor884 checked884 (hRep descriptor884.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0304.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0304.regionContext := by
  apply Generated.FunctionalChunk0304.valid
  · exact leaf882 hRep
  · exact leaf883 hRep
  · exact leaf884 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0304

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0305
def descriptor885 : OrbitDescriptor := ⟨63, 6, true⟩

theorem checked885 : orbitPatternTransform descriptor885 (Generated.Chunk0305.pattern885) =
    orbitRepresentativePattern descriptor885.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf885 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0305.pattern885 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0305.pattern885) descriptor885 checked885 (hRep descriptor885.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0305.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0305.regionContext := by
  apply Generated.FunctionalChunk0305.valid
  · exact leaf885 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0305

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0306
def descriptor886 : OrbitDescriptor := ⟨27, 10, true⟩

theorem checked886 : orbitPatternTransform descriptor886 (Generated.Chunk0306.pattern886) =
    orbitRepresentativePattern descriptor886.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf886 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0306.pattern886 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0306.pattern886) descriptor886 checked886 (hRep descriptor886.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0306.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0306.regionContext := by
  apply Generated.FunctionalChunk0306.valid
  · exact leaf886 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0306

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0307
def descriptor887 : OrbitDescriptor := ⟨35, 8, true⟩

theorem checked887 : orbitPatternTransform descriptor887 (Generated.Chunk0307.pattern887) =
    orbitRepresentativePattern descriptor887.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf887 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0307.pattern887 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0307.pattern887) descriptor887 checked887 (hRep descriptor887.representative)

def descriptor888 : OrbitDescriptor := ⟨34, 8, true⟩

theorem checked888 : orbitPatternTransform descriptor888 (Generated.Chunk0307.pattern888) =
    orbitRepresentativePattern descriptor888.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf888 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0307.pattern888 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0307.pattern888) descriptor888 checked888 (hRep descriptor888.representative)

def descriptor889 : OrbitDescriptor := ⟨33, 8, true⟩

theorem checked889 : orbitPatternTransform descriptor889 (Generated.Chunk0307.pattern889) =
    orbitRepresentativePattern descriptor889.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf889 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0307.pattern889 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0307.pattern889) descriptor889 checked889 (hRep descriptor889.representative)

def descriptor890 : OrbitDescriptor := ⟨32, 14, true⟩

theorem checked890 : orbitPatternTransform descriptor890 (Generated.Chunk0307.pattern890) =
    orbitRepresentativePattern descriptor890.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf890 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0307.pattern890 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0307.pattern890) descriptor890 checked890 (hRep descriptor890.representative)

def descriptor891 : OrbitDescriptor := ⟨30, 14, true⟩

theorem checked891 : orbitPatternTransform descriptor891 (Generated.Chunk0307.pattern891) =
    orbitRepresentativePattern descriptor891.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf891 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0307.pattern891 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0307.pattern891) descriptor891 checked891 (hRep descriptor891.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0307.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0307.regionContext := by
  apply Generated.FunctionalChunk0307.valid
  · exact leaf887 hRep
  · exact leaf888 hRep
  · exact leaf889 hRep
  · exact leaf890 hRep
  · exact leaf891 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0307

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0308
def descriptor892 : OrbitDescriptor := ⟨32, 8, true⟩

theorem checked892 : orbitPatternTransform descriptor892 (Generated.Chunk0308.pattern892) =
    orbitRepresentativePattern descriptor892.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf892 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0308.pattern892 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0308.pattern892) descriptor892 checked892 (hRep descriptor892.representative)

def descriptor893 : OrbitDescriptor := ⟨31, 8, true⟩

theorem checked893 : orbitPatternTransform descriptor893 (Generated.Chunk0308.pattern893) =
    orbitRepresentativePattern descriptor893.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf893 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0308.pattern893 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0308.pattern893) descriptor893 checked893 (hRep descriptor893.representative)

def descriptor894 : OrbitDescriptor := ⟨29, 14, true⟩

theorem checked894 : orbitPatternTransform descriptor894 (Generated.Chunk0308.pattern894) =
    orbitRepresentativePattern descriptor894.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf894 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0308.pattern894 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0308.pattern894) descriptor894 checked894 (hRep descriptor894.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0308.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0308.regionContext := by
  apply Generated.FunctionalChunk0308.valid
  · exact leaf892 hRep
  · exact leaf893 hRep
  · exact leaf894 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0308

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0309
def descriptor895 : OrbitDescriptor := ⟨30, 8, true⟩

theorem checked895 : orbitPatternTransform descriptor895 (Generated.Chunk0309.pattern895) =
    orbitRepresentativePattern descriptor895.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf895 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0309.pattern895 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0309.pattern895) descriptor895 checked895 (hRep descriptor895.representative)

def descriptor896 : OrbitDescriptor := ⟨29, 8, true⟩

theorem checked896 : orbitPatternTransform descriptor896 (Generated.Chunk0309.pattern896) =
    orbitRepresentativePattern descriptor896.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf896 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0309.pattern896 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0309.pattern896) descriptor896 checked896 (hRep descriptor896.representative)

def descriptor897 : OrbitDescriptor := ⟨28, 8, true⟩

theorem checked897 : orbitPatternTransform descriptor897 (Generated.Chunk0309.pattern897) =
    orbitRepresentativePattern descriptor897.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf897 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0309.pattern897 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0309.pattern897) descriptor897 checked897 (hRep descriptor897.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0309.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0309.regionContext := by
  apply Generated.FunctionalChunk0309.valid
  · exact leaf895 hRep
  · exact leaf896 hRep
  · exact leaf897 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0309

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0310
def descriptor898 : OrbitDescriptor := ⟨27, 8, true⟩

theorem checked898 : orbitPatternTransform descriptor898 (Generated.Chunk0310.pattern898) =
    orbitRepresentativePattern descriptor898.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf898 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0310.pattern898 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0310.pattern898) descriptor898 checked898 (hRep descriptor898.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0310.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0310.regionContext := by
  apply Generated.FunctionalChunk0310.valid
  · exact leaf898 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0310

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0311
def descriptor899 : OrbitDescriptor := ⟨1, 9, true⟩

theorem checked899 : orbitPatternTransform descriptor899 (Generated.Chunk0311.pattern899) =
    orbitRepresentativePattern descriptor899.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf899 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0311.pattern899 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0311.pattern899) descriptor899 checked899 (hRep descriptor899.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0311.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0311.regionContext := by
  apply Generated.FunctionalChunk0311.valid
  · exact leaf899 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0311
