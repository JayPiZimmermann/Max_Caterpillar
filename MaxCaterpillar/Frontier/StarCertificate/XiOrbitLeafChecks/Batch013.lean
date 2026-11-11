import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0104
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0105
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0106
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0107
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0108
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0109
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0110
import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk0111
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0104
def descriptor288 : OrbitDescriptor := ⟨54, 1, false⟩

theorem checked288 : orbitPatternTransform descriptor288 (Generated.Chunk0104.pattern288) =
    orbitRepresentativePattern descriptor288.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf288 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0104.pattern288 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0104.pattern288) descriptor288 checked288 (hRep descriptor288.representative)

def descriptor289 : OrbitDescriptor := ⟨58, 17, true⟩

theorem checked289 : orbitPatternTransform descriptor289 (Generated.Chunk0104.pattern289) =
    orbitRepresentativePattern descriptor289.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf289 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0104.pattern289 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0104.pattern289) descriptor289 checked289 (hRep descriptor289.representative)

def descriptor290 : OrbitDescriptor := ⟨45, 17, true⟩

theorem checked290 : orbitPatternTransform descriptor290 (Generated.Chunk0104.pattern290) =
    orbitRepresentativePattern descriptor290.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf290 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0104.pattern290 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0104.pattern290) descriptor290 checked290 (hRep descriptor290.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0104.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0104.regionContext := by
  apply Generated.FunctionalChunk0104.valid
  · exact leaf288 hRep
  · exact leaf289 hRep
  · exact leaf290 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0104

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0105
def descriptor291 : OrbitDescriptor := ⟨58, 16, true⟩

theorem checked291 : orbitPatternTransform descriptor291 (Generated.Chunk0105.pattern291) =
    orbitRepresentativePattern descriptor291.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf291 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0105.pattern291 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0105.pattern291) descriptor291 checked291 (hRep descriptor291.representative)

def descriptor292 : OrbitDescriptor := ⟨55, 16, true⟩

theorem checked292 : orbitPatternTransform descriptor292 (Generated.Chunk0105.pattern292) =
    orbitRepresentativePattern descriptor292.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf292 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0105.pattern292 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0105.pattern292) descriptor292 checked292 (hRep descriptor292.representative)

def descriptor293 : OrbitDescriptor := ⟨42, 17, true⟩

theorem checked293 : orbitPatternTransform descriptor293 (Generated.Chunk0105.pattern293) =
    orbitRepresentativePattern descriptor293.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf293 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0105.pattern293 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0105.pattern293) descriptor293 checked293 (hRep descriptor293.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0105.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0105.regionContext := by
  apply Generated.FunctionalChunk0105.valid
  · exact leaf291 hRep
  · exact leaf292 hRep
  · exact leaf293 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0105

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0106
def descriptor294 : OrbitDescriptor := ⟨45, 16, true⟩

theorem checked294 : orbitPatternTransform descriptor294 (Generated.Chunk0106.pattern294) =
    orbitRepresentativePattern descriptor294.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf294 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0106.pattern294 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0106.pattern294) descriptor294 checked294 (hRep descriptor294.representative)

def descriptor295 : OrbitDescriptor := ⟨42, 16, true⟩

theorem checked295 : orbitPatternTransform descriptor295 (Generated.Chunk0106.pattern295) =
    orbitRepresentativePattern descriptor295.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf295 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0106.pattern295 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0106.pattern295) descriptor295 checked295 (hRep descriptor295.representative)

def descriptor296 : OrbitDescriptor := ⟨38, 16, true⟩

theorem checked296 : orbitPatternTransform descriptor296 (Generated.Chunk0106.pattern296) =
    orbitRepresentativePattern descriptor296.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf296 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0106.pattern296 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0106.pattern296) descriptor296 checked296 (hRep descriptor296.representative)

def descriptor297 : OrbitDescriptor := ⟨37, 16, true⟩

theorem checked297 : orbitPatternTransform descriptor297 (Generated.Chunk0106.pattern297) =
    orbitRepresentativePattern descriptor297.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf297 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0106.pattern297 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0106.pattern297) descriptor297 checked297 (hRep descriptor297.representative)

def descriptor298 : OrbitDescriptor := ⟨36, 16, true⟩

theorem checked298 : orbitPatternTransform descriptor298 (Generated.Chunk0106.pattern298) =
    orbitRepresentativePattern descriptor298.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf298 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0106.pattern298 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0106.pattern298) descriptor298 checked298 (hRep descriptor298.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0106.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0106.regionContext := by
  apply Generated.FunctionalChunk0106.valid
  · exact leaf294 hRep
  · exact leaf295 hRep
  · exact leaf296 hRep
  · exact leaf297 hRep
  · exact leaf298 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0106

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0107
def descriptor299 : OrbitDescriptor := ⟨1, 3, false⟩

theorem checked299 : orbitPatternTransform descriptor299 (Generated.Chunk0107.pattern299) =
    orbitRepresentativePattern descriptor299.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf299 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0107.pattern299 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0107.pattern299) descriptor299 checked299 (hRep descriptor299.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0107.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0107.regionContext := by
  apply Generated.FunctionalChunk0107.valid
  · exact leaf299 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0107

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0108
def descriptor300 : OrbitDescriptor := ⟨27, 2, false⟩

theorem checked300 : orbitPatternTransform descriptor300 (Generated.Chunk0108.pattern300) =
    orbitRepresentativePattern descriptor300.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf300 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0108.pattern300 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0108.pattern300) descriptor300 checked300 (hRep descriptor300.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0108.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0108.regionContext := by
  apply Generated.FunctionalChunk0108.valid
  · exact leaf300 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0108

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0109
def descriptor301 : OrbitDescriptor := ⟨28, 2, false⟩

theorem checked301 : orbitPatternTransform descriptor301 (Generated.Chunk0109.pattern301) =
    orbitRepresentativePattern descriptor301.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf301 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0109.pattern301 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0109.pattern301) descriptor301 checked301 (hRep descriptor301.representative)

def descriptor302 : OrbitDescriptor := ⟨29, 2, false⟩

theorem checked302 : orbitPatternTransform descriptor302 (Generated.Chunk0109.pattern302) =
    orbitRepresentativePattern descriptor302.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf302 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0109.pattern302 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0109.pattern302) descriptor302 checked302 (hRep descriptor302.representative)

def descriptor303 : OrbitDescriptor := ⟨30, 2, false⟩

theorem checked303 : orbitPatternTransform descriptor303 (Generated.Chunk0109.pattern303) =
    orbitRepresentativePattern descriptor303.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf303 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0109.pattern303 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0109.pattern303) descriptor303 checked303 (hRep descriptor303.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0109.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0109.regionContext := by
  apply Generated.FunctionalChunk0109.valid
  · exact leaf301 hRep
  · exact leaf302 hRep
  · exact leaf303 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0109

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0110
def descriptor304 : OrbitDescriptor := ⟨29, 12, false⟩

theorem checked304 : orbitPatternTransform descriptor304 (Generated.Chunk0110.pattern304) =
    orbitRepresentativePattern descriptor304.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf304 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0110.pattern304 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0110.pattern304) descriptor304 checked304 (hRep descriptor304.representative)

def descriptor305 : OrbitDescriptor := ⟨31, 2, false⟩

theorem checked305 : orbitPatternTransform descriptor305 (Generated.Chunk0110.pattern305) =
    orbitRepresentativePattern descriptor305.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf305 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0110.pattern305 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0110.pattern305) descriptor305 checked305 (hRep descriptor305.representative)

def descriptor306 : OrbitDescriptor := ⟨32, 2, false⟩

theorem checked306 : orbitPatternTransform descriptor306 (Generated.Chunk0110.pattern306) =
    orbitRepresentativePattern descriptor306.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf306 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0110.pattern306 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0110.pattern306) descriptor306 checked306 (hRep descriptor306.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0110.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0110.regionContext := by
  apply Generated.FunctionalChunk0110.valid
  · exact leaf304 hRep
  · exact leaf305 hRep
  · exact leaf306 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0110

namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0111
def descriptor307 : OrbitDescriptor := ⟨30, 12, false⟩

theorem checked307 : orbitPatternTransform descriptor307 (Generated.Chunk0111.pattern307) =
    orbitRepresentativePattern descriptor307.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf307 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0111.pattern307 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0111.pattern307) descriptor307 checked307 (hRep descriptor307.representative)

def descriptor308 : OrbitDescriptor := ⟨32, 12, false⟩

theorem checked308 : orbitPatternTransform descriptor308 (Generated.Chunk0111.pattern308) =
    orbitRepresentativePattern descriptor308.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf308 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0111.pattern308 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0111.pattern308) descriptor308 checked308 (hRep descriptor308.representative)

def descriptor309 : OrbitDescriptor := ⟨33, 2, false⟩

theorem checked309 : orbitPatternTransform descriptor309 (Generated.Chunk0111.pattern309) =
    orbitRepresentativePattern descriptor309.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf309 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0111.pattern309 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0111.pattern309) descriptor309 checked309 (hRep descriptor309.representative)

def descriptor310 : OrbitDescriptor := ⟨34, 2, false⟩

theorem checked310 : orbitPatternTransform descriptor310 (Generated.Chunk0111.pattern310) =
    orbitRepresentativePattern descriptor310.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf310 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0111.pattern310 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0111.pattern310) descriptor310 checked310 (hRep descriptor310.representative)

def descriptor311 : OrbitDescriptor := ⟨35, 2, false⟩

theorem checked311 : orbitPatternTransform descriptor311 (Generated.Chunk0111.pattern311) =
    orbitRepresentativePattern descriptor311.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)

theorem leaf311 (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    ∀ z, actualSigns subsetForms z = Generated.Chunk0111.pattern311 → AllStarAnovaZero z :=
  orbit_reduce_pattern (Generated.Chunk0111.pattern311) descriptor311 checked311 (hRep descriptor311.representative)

theorem valid (hRep : (∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)) :
    Generated.Chunk0111.tree.FunctionalValid starIntegerSubsetForms
      (fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z) Generated.Chunk0111.regionContext := by
  apply Generated.FunctionalChunk0111.valid
  · exact leaf307 hRep
  · exact leaf308 hRep
  · exact leaf309 hRep
  · exact leaf310 hRep
  · exact leaf311 hRep
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Chunk0111
